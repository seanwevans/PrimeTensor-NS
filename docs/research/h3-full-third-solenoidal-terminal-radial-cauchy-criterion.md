# Terminal spectral H³ Cauchy criterion and cofinal high-radial escape

**Base HEAD:** `5e9dcc2006f8138e1826d6de8cdc50ba8ac721d1` — prove compact-time solenoidal H³ Fourier flux tail tightness.

## Hard-math checkpoint

Let `U : ℝ → H3SpectralVelocityState` be the **genuine** weighted H³ Fourier velocity path, and let `P_R` be the verified high-radial indicator operator already used in the three-sector complex trilinear flux theorem. Define `Q_R U = U - P_R U`.

Then the exact decomposition and triangle inequality give, for any times `s,t` and radius `R`,

```
‖U(s) - U(t)‖ ≤
  ‖Q_R U(s) - Q_R U(t)‖ + ‖P_R U(s)‖ + ‖P_R U(t)‖.
```

### Terminal criterion

Assume:

1. **Fixed-band temporal Cauchy:** For every `R` and `ε>0`, the low-band states `Q_R U(t)` are mutually `ε`-close for all `s,t` sufficiently near `T` from below.
2. **Endpoint-uniform high-radial tightness:** For each `ε>0` there are one cutoff `R` and terminal neighborhood `(T-δ,T)` such that `‖P_R U(t)‖<ε` for every time in that neighborhood.

Choosing the radius at tail tolerance `ε/4`, then the temporal window at low-band tolerance `ε/2`, gives full terminal Cauchy. Completeness of the actual H³ spectral state gives the **strong terminal H³ trace**.

### Quantified high-radial obstruction

Assuming fixed-band Cauchy, failure of the strong weighted H³ terminal trace forces

```
∃ ε > 0, ∀ R : ℕ, ∀ δ > 0, ∃ t ∈ (a,T),
  T - t < δ ∧ ε ≤ ‖P_R U(t)‖.
```

This is the precise endpoint quantifier order: the positive obstruction threshold is chosen *before* any fixed cutoff or terminal neighborhood. It does not assert the strength or sign of the full trilinear flux, whose existing upper bound is one-sided.

## Established inputs reused

- `thirdFullSpectralVelocityHighRadialApply244` and its exact high-frequency representation, contraction and decay.
- `h3AuditActualSpectralVelocityTotal hH3`, the original physical weighted H³ spectral trajectory.
- `cauchy_map_iff_exists_tendsto` and Hilbert completeness for the actual spectral velocity space.
- Previous compact-time tightness, which remains restricted to compact intervals strictly inside `(0,T)`.

## Remaining PDE frontier

The existing `h3Critical_actualPhysicalSharpLowCutoff_source_intervalIntegrable` establishes Bochner-`L¹` control of each *physical kinetic* low-frequency projected source over strict terminal tails without H³ norm boundedness. The next hard step is to transport that fact through the exact physical evolution/Bochner FTC and the finite-band weighted Fourier multiplier to discharge the `ThirdFullTerminalLowRadialCauchyOn244` premise **unconditionally** for the actual H³ trajectory. This patch does not silently identify weighted spectral low-band increments with physical kinetic increments.

After that step, terminal H³ nonconvergence would imply the explicit cofinal high-radial weighted H³ mass escape above. The distinct work of excluding that escape using endpoint dissipation and nonlinear transport remains open. No global Navier–Stokes regularity claim is made here.

## Validation contract

- Register both modules in `PrimeTensor.lean` and `tools/audit/FirstMonomialTriad.lean`.
- Generate/check the source index and fragment index.
- `lake env lean` each file, `lake build` each module, full `lake build`, baseline reuse-build audit.
- `#check` and `#print axioms` every theorem and definition; no new axiom/sorry/admit.
- Stage regenerated index after complete build, check staged whitespace, commit and push only if all checks succeed.

## Lean elaboration fix 1

The last line of the triangle-inequality calculation explicitly applies `norm_sub_le` to the **high-radial** projections, not to the low-radial projections. It uses `add_le_add le_rfl` to preserve the low-band difference term unchanged. Two terminal-neighborhood membership proofs now first give the open-ray inclusions as typed `∀ᶠ` statements in `𝓝 T`, then transfer them to `𝓝[<] T` with `filter_mono nhdsWithin_le_nhds`. No statement, assumption, or constant changed.
