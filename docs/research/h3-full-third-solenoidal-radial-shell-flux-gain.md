# Pure sixth-power H³ transfer: quantitative radial-shell gain

Base: `ad10507c11fdea3b0694ed1ccf2e175620041041` — the longitudinal defect has been eliminated on the actual solenoidal Schwartz density sequence, so the signed physical H³ transport is the limit of the *uncorrected* sixth-power complex Fourier flux.

## Pointwise identity and estimate

For Fourier triad `p+q+r=0`, let `P=|p|²`, `Q=|q|²`, `R=|r|²`, `S=max(P,Q,R)`, and `Δ=S-min(P,Q,R)`. Let `X`, `Y`, `Z` be the **actual complex** polarization contractions

- `X=(A·C)(r·B)`;
- `Y=(A·B)(q·C)`;
- `Z=(B·C)(r·A)`.

The three-transfer flux is exactly

`F6 = X(R³-P³) + Y(Q³-P³) + Z(R³-Q³)`.

For `0 ≤ x,y ≤ S`, factor the real cube difference:

`|x³-y³| = |x-y|(x²+xy+y²) ≤ 3 S² |x-y|`.

Since every pair of squared radii differs by at most `Δ`, the full complex estimate is

`‖F6‖ ≤ 3 S² Δ (‖X‖ + ‖Y‖ + ‖Z‖)`.

No polarization is conjugated, the zero frequency is included, and no reciprocal radius is introduced.

If `lo ≤ P,Q,R ≤ hi` with `0 ≤ lo ≤ hi`, then the **annular gain** is

`‖F6‖ ≤ 3 hi² (hi-lo)(‖X‖+‖Y‖+‖Z‖)`.

The exact equal-radius vanishing is a corollary, while any nonzero flux forces `Δ>0`. The estimate applies to the actual Schwartz Fourier amplitudes, not just frozen polynomial symbols.

## Important limitation

This is a *pointwise triad estimate*, not yet a stronger H³ energy absorption inequality. The full physical flux integrates across all radial combinations and its Fourier amplitude budget can grow as the annulus narrows. To convert this geometric gain to a coercive bound, we must prove either a weighted integrability estimate for the contraction budget or a quantitative tail decomposition controlling off-annulus interactions along the same solenoidal Schwartz sequence. Neither conclusion is assumed here.

## Validation

Run the registrar `--apply` / `--check`, `proof/generate_index.py` and its `--check`, Lean single-module elaboration, the focused Lake build, fragment audit, then the full Lake build. Check `#print axioms` for each declared theorem and definition. No new axioms, `sorry`, or `admit` are present in this source. Static checks are not Lean compilation.
