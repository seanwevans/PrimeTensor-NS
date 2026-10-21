# Exact signed global fifth/cubic Fourier phase defect

Base checkpoint: `3f71ae5c` — parameterize signed fifth radial absorption against cubic Leray forcing.

## Recover the nonnegative remainder discarded by Young

The global physical top-dissipation PDE identity is

    D3'(t) = -2 M5(t) + F_global(t),
    F_global(t) = -2 Σ_j ∫ q^4 Re⟪û_j, F_j(U,U)⟫.

The previous Young estimate `D3' + M5 ≤ M3` discards the spectral phase mismatch. For any nonnegative Fourier squared-gradient frequency q and complex velocity/forcing coordinates z and f, define

    Q(q,z,f) = q^5 |z|² + q^3 |f|² + 2 q^4 Re⟪z,f⟫.

The exact real square expansion is

    Q = q^3 (q|z|-|f|)²
          + 2 q^4 (|z||f|+Re⟪z,f⟫) ≥ q^3(q|z|-|f|)² ≥ 0.

The first term detects the **amplitude mismatch** `q|z| != |f|`; the second detects failure of **opposite phase** alignment. The integral is finite at each strict physical time because `q⁵|z|²`, `q³|f|²`, and `q⁴Re⟪z,f⟫` are already integrable by the Fourier Hilbert PDE factorization and forcing-moment construction.

Defining the physical global signed defect

    P(t) = Σ_j ∫ Q(q(ξ),û_j(t,ξ),F_j(t,ξ)) dξ,

the new equality is

    P(t) = M5(t) + M3(t) - F_global(t) ≥ 0,

hence the genuine signed PDE equation is the **exact balance**

    D3'(t) + M5(t) + P(t) = M3(t).

Unlike an adjustable Young bound, this keeps the complete positive remainder. For `D3' ≥ 0`, the cubic forcing must cover both the fifth velocity moment and the phase defect:

    M3(t) ≥ M5(t) + P(t).

The equality does not eliminate a singularity. It exposes a further spectral **necessary** cancellation mechanism: rapidly growing top dissipation demands cubic forcing sufficient to pay for viscous mass *and* amplitude/phase discrepancy. Because normalized variance contains `-E2² E0 D3'`, this identity cannot be substituted in the wrong inequality orientation to claim anti-concentration.

## Next mathematical issue

Relate the middle Fourier moment's *actual signed PDE evolution* to `P(t)`, preferably through a common velocity/forcing amplitude and phase coordinate. An inequality controlling `R'` in terms of the phase defect would be genuinely stronger than further optimizing the Young constant. The phase mismatch is explicitly nonnegative, but no positive terminal lower bound for it has been proved.

## Audit

Register two definitions and seven theorems with `#check` / `#print axioms` in the first-monomial audit; update PrimeTensor import and proof index, check fragments, compile local module and full library, run baseline, push only on success.
