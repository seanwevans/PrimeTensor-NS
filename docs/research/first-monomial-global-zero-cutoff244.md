# Exact global heat / Leray decomposition at zero radial cutoff

Base commit: `64b6aad7` — exact split of physical H3 signed excess into
radial heat, Leray forcing and low complement at natural cutoff `n + 1`.

## Eliminate the cut-off seam without exchanging derivatives and limits

The natural-cutoff theorem includes a low-frequency derivative correction
because each cutoff is `n + 1` and therefore excludes a genuine positive
ball. Letting `n → ∞` would make that omitted ball **larger**, not smaller.
It does not eliminate the low complement.

The repository's strong Hilbert pairing theorem, however, was proved for an
**arbitrary real cutoff** `R`; this includes `R = 0`. The Fourier gradient
magnitude is nonnegative, so `h3TerminalRadialFrequencyBelow 0 = ∅`. Its
complement is all frequencies, and the restriction map preserves the full
Hilbert pairing. The previously closed real-coordinate PDE pairing thus
identifies directly the true global fourth-radial derivative:

    D3'(t) = Heat_global(t) + Leray_global(t),

where

    Heat_global(t) = -2 Σ_j ∫ q^5 |û_j|² ≤ 0,
    Leray_global(t) = -2 Σ_j ∫ q^4 Re⟪û_j,F_j(U,U)⟫.

The scalar integrals are bona fide integrable at strict times by the
existing Fourier Hilbert `L² × L² → L¹` theorems. The cutoff is fixed to zero,
so no derivative-limit interchange or claimed vanishing from a positive
cutoff is involved.

Combining with already-closed lower-order spatial PDE energy splitting,
pressure cancellation and zeroth-order transport cancellation yields:

    X(t) = B_global(t) + N_global(t),
    B_global = 2 E2 L2 (E0 D3) - E2²(L0 D3 + E0 Heat_global),
    N_global = -2 E2 T2 (E0 D3) - E2² E0 Leray_global.

The signed source X already satisfies `R' = -X/(E0 D3)^2` for the physical
normalized Fourier variance R. An exact secant and near-Young estimate
therefore force global heat-plus-Leray production at some interior time.

## Scope and limitations

* The global heat term is nonpositive, but this does NOT mean the heat part
  of normalized variance has a definite sign; the moment quotient includes
  lower-order heat terms.
* No upper bound on the nonlinear Leray transfer is proved here.
* No uniform anti-concentration bound or unconditional smooth continuation
  follows from the decomposition alone.

The next analytic task is comparing global heat moment ratios and the actual
order-two transport plus fourth-radial Leray transfer, without allowing a
terminal concentration rate unsupported by the PDE.

## Audit

Register module in `PrimeTensor.lean`, central `FirstMonomialTriad` audit,
`#check` and `#print axioms` for all declarations. Regenerate index, verify
fragments, compile module, central audit, and full library, run baseline.
