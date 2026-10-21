# Global normalized Leray production versus the full-space absolute transfer

Base checkpoint: `dd1da994` — the unconditional physical viscous ceiling and exact global signed Leray secant.

## Bridge between two already-closed Fourier PDE programs

The zero-cutoff energy evolution yields an actual global signed fourth-radial nonlinear term

    F_global(t) = -2 Σ_j ∫ q^4 Re <u_j, F_j(U,U)>.

The earlier terminal top-dissipation program introduced the **same** strict-time integrable Fourier density and constructed the cutoff-independent profile

    G(t) = 2 Σ_j ∫ q^4 |Re <u_j, F_j(U,U)>| >= 0.

Taking the *reverse* sign of the Fourier integral gives the new physical comparison

    -F_global(t) <= G(t).

Its proof invokes the existing `integrable_h3TerminalPhysicalTopDissipationNonlinearCoordinateDensityAt'`, so no new Lebesgue-product theorem is assumed. This sign is crucial: the normalized spectral concentration rate contains `-E2^2 E0 F_global / (E0 D3)^2`, rather than the usual positive top-tail nonlinear transfer.

The already-closed Fourier first-Cauchy inequality `E2^2 <= E0 D3` and positive `E0,D3` show

    F_Leray_normalized(t) <= G(t) / D3(t).

This is exact physical normalization, not an assumed terminal uniform estimate. The factor `E0` cancels, while `D3` remains in the denominator.

## Fully explicit global concentration ceiling

Earlier `GlobalViscousCeiling244` established

    X/(E0 D3)^2 <= V(t) + 36 C1 sqrt(E_H3(t)) + F_Leray_normalized(t),

where the viscous ceiling `V(t) = -(L0 D3 + E0 Heat5)/(E0 D3)` uses the actual zeroth-order diffusion loss and full fifth-radial heat rate. Hence the new theorem gives

    X/(E0 D3)^2 <= V(t) + 36 C1 sqrt(E_H3(t)) + G(t)/D3(t).

Under the established near-Young hypotheses on `[s,t]`, the genuine secant at a strict interior time `r` forces

    G(r)/D3(r) >=
      [R(s) - 256 delta/(27 K^4 E0(t))]/(t-s)
      - 36 C1 sqrt(E_H3(r)) - V(r).

This connects the normalized variance corridor directly to the earlier cutoff-uniform full-space nonlinear-transfer criterion. It neither claims that `G/D3` is integrable nor infers that `G` itself must diverge: the denominator `D3` may vary, and the fifth moment in `V` may grow. Those are the remaining analytic questions.

## Scope and validation

One definition and six theorems use the existing physical H3 class, the strict-time Fourier integrability established in `Transfer.Majorant`, and the already proved zero-cutoff, commutator and viscous-ceiling theorems. There are no new PDE hypotheses, axioms, or proof placeholders. The package contains an idempotent audit registrar and this research note; run `proof/generate_index.py` and the complete Lean and baseline checks before committing.
