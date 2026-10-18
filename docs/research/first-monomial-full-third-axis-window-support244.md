# Full-third Hermitian window support on the physical axis carrier

Base commit: `64eb44f8` — projected full-third Hermitian germ and windowed sign.

The existing low-normal packet construction used `Fin 3 → ℝ` while the
seven-derivative corrected full-third physical symbol uses
`Axis Depth.three → ℝ`. This patch transfers the twelve coherent label
classification at `t = 1` to the latter carrier via coordinate readback.

The six centers correspond to `(1,0,0)`, `(1,1,0)`, `(-2,-1,0)` and
reflections. Every zero-momentum triple inside sufficiently narrow
compact, smooth center windows has coherent labels. The width bound is
`ρ ≤ lowNormalSixCenterSeparationRadius 1` (equivalently `ρ ≤ 1/4`).

Each actual-axis center cutoff is smooth, compactly supported, equals one at
its designated center, and its nonzero support lies inside its open center
ball. The final theorem is
`thirdFullAxisWindowBump_zero_sum_coherent244`. The momentum-plane
corollary `thirdFullAxisWindowBump_noncoherent_product_zero244`
proves the exact three-window factor is zero in all noncoherent sectors.

This bridges support geometry, not Fourier phases or the global physical
noncancellation. Next: construct the Hermitian vector-valued Schwartz
packet on the exact carrier, retain the complex phase in all 12 coherent
sectors, and identify/estimate the actual full-third Fourier integral.

**Verification:** The proof has not been compiled in an assistant-side Lean
environment. Run `lake env lean` and `lake build` on your checkout before
committing.
