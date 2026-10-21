# Full absolute Leray transfer: fifth velocity and cubic forcing masses

Base commit: `164aa3e6` — bridge global normalized Leray concentration to the full absolute-transfer profile.

## Physical bridge

At each strict physical H3 slice, with `q = h3FourierGradientSquare ξ ≥ 0`, actual spectral velocity `z_j`, and the genuine Leray forcing `f_j`, the established profile is

    G = 2 Σ_j ∫ q⁴ |Re ⟪z_j,f_j⟫|.

The previously constructed forcing mass and the newly named fifth velocity mass are

    M3 = Σ_j ∫ q³ |f_j|²,
    M5 = Σ_j ∫ q⁵ |z_j|².

The pointwise inequality, preserving all Fourier weights, is

    2 q⁴ |Re ⟪z,f⟫| ≤ 2 q⁴ |z| |f|
                         ≤ q⁵ |z|² + q³ |f|².

The second step is exactly `0 ≤ q³ (q|z| - |f|)²`. The existing Hilbert PDE factorization, fifth-moment integrability, and cubic forcing integrability justify the global integrals. Consequently:

    G(t) ≤ M5(t) + M3(t),
    G(t)/D3(t) ≤ (M5(t)+M3(t))/D3(t)   [D3(t)>0].

The near-Young signed secant then forces the **two-moment normalized sum** to exceed the explicit residual concentration threshold at an interior time, after deducting only the already-proved order-two and viscous budgets.

## Critical sign audit

This result does **not** justify simply cancelling `M5` against the signed heat contribution in an *upper bound on concentration*. The exact fourth-radial heat rate is `-2 M5`. In the signed concentration excess it enters through `-E2² E0 D3'`, so a large negative `D3'` contributes **positively** to spectral concentration. The orientation of any absorption argument must respect this fact.

The result reduces the absolute-transfer obstruction to the concrete pair `M5+M3` but supplies no terminal-uniform bound, no integrability of the normalized sum, and no unconditional Navier–Stokes continuation.

## Audit/build

Register the module in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`, run `proof/generate_index.py`, `proof/check_fragment.py --all`, local module compile, central audit compile, full `lake build`, and baseline audit. All five declarations receive `#check` and `#print axioms`.
