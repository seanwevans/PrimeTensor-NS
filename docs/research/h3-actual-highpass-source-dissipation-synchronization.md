# Same-time high-pass source mass and high-H³ dissipation escape

**Base:** `34f213ee` (actual physical projected source high-pass Fourier mass escape; Lean CI successful).

The existing results individually give cofinal high-frequency projected-source
Fourier mass spikes and cofinal high-radial H³ dissipation spikes under failure
of the strong physical L² terminal velocity trace. They do not synchronize
those times. The new exact low/high H³ dissipation partition and physical
projected source estimate yield the pointwise, synchronized bound, with
`U(t)` the actual weighted H³ spectral velocity:

```
||1_{Sρᶜ} R̂_i(t)||₂
  <= (3 + C_L) * (1 + 6 E₀(b) + 3 * (σ² Wσ² E₀(b) + D_{>σ}(t)))
```

`ρ` and `σ` are independent nonnegative fixed radii. Crucially, the
complementary Fourier cutoff is a contraction, rather than being bounded
via the triangle inequality with an extraneous factor two.

The same-time theorem fixes **one coordinate i before radii and thresholds**
and yields, for any strict later tail `(c,T)` and any real `K,M`, a single
time `t∈(c,T)` at which the actual projected-source Fourier square mass above
radius `ρ` exceeds `K` **and** the actual physical H³ spectral dissipation
above `σ` exceeds `M`. The argument chooses a source-mass threshold above the
square of the high-dissipation conditional bound; a smaller dissipation
would contradict that mass spike at the very same time.

The hypothesis of no strong terminal physical L² trace remains explicit.
The theorem neither proves that this failure occurs nor precludes the
compensating nonlinear transport and temporal concentration mechanisms.

## Verification

The registrar checks five theorem names and their `#print axioms` audit lines.
Static ZIP, check and idempotence checks are not Lean compilation. Run the
associated targeted `lake build` and the full project baseline locally.
