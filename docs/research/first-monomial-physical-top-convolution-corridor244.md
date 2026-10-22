# Physical third-radial forcing escape: fourth-order velocity convolution corridor

Base: `07e2aabc` — freeze a fixed cofinal third-radial Leray forcing component.

The project already proves that unbounded physical fourth-radial top dissipation implies one **fixed** third-radial nonlinear Leray coordinate `i₀` with arbitrarily large weighted `L²` mass on every terminal subtail.

The earlier radial Young product theorem states, for radial order `m=3`,

    ‖ |ξ|³ P div(U⊗U)_{i₀} ‖₂
      ≤ ∑_{k=0}² 2 * ∑_{j=0}² (2π) ‖ |ξ|⁴ (Û_k * Û_j) ‖₂.

Every term on the right is an **actual** velocity Fourier convolution. The factor `2` bounds the Leray matrix row and `2π` is the divergence symbol factor. The state construction permits identifying the left side with the existing physical forcing Hilbert path by equality of almost-everywhere representatives.

## Quantitative consequence

Since the right side has nine terms, if every order-four pair-convolution norm were at most `K`, the RHS would be at most `36π K`. The committed cofinal escape therefore forces, on every strict terminal subtail and for every real threshold `K`, some (possibly time-dependent) ordered pair `(k,j)` whose actual fourth-radial product convolution `L²` norm exceeds `K`.

The input hypotheses are explicit: `H3RawFourierMomentIntegrable 8` is required for each velocity spectral component at every strict time. The patch **does not claim** that an H³ energy bound alone provides eighth-order Fourier moments, or that a **fixed** ordered pair is obtained cofinally. The forcing coordinate `i₀` remains fixed, while the product pair can change with threshold and time.

## Next analytic gap

The resulting necessary product-convolution corridor still does not exclude terminal escape. The next steps would be to derive high raw velocity moments automatically on strict slabs, then use the existing convolution-moment inequality to force a quantitative factor escape and distinguish low/high radial input sources. These require nontrivial PDE information rather than further finite pigeonhole alone.
