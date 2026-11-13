# Actual selected annular excess forces aspect escape at natural moving radii

**Parent:** `9b513d7f38380e86f1b055b3c858147a898f8a7c` — replace vacuous annular rectangles with selected cofinal physical clocks.

## Mathematical issue

The preceding selected-pair argument correctly removed an impossible rectangular-annulus positive-excess hypothesis. Its bounded-aspect obstruction `thirdFullPhysical_selectedBoundedAspect_noHighpassTightness244` still accepted the vanishing of the **actual sharp physical highpass kinetic mass** as an independent premise.

## Exact physical highpass bridge

For any real three-component physical velocity `V` and natural cutoff `rho = n+1`, Plancherel, the actual sharp physical Fourier projector, and the `PiLp 2` square identity yield

```
||V - P_{n+1} V||_{L2(real)^3}^2
  <= 3 ||High_n(RawFourier(V))||_{(L2(C))^3, sup}^2.
```

The factor three comes from the three actual physical components and the native spectral finite-product sup norm, rather than inventing an isometric norm equivalence between these different product norms.

The existing `thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244` already proves that the RHS goes to zero whenever `V_k -> V_T` strongly in physical L² and `n_k -> ∞`.

## Actual terminal trace and selected geometry

The previously established `h3Critical_physicalL2_terminal_trace_of_finite_dissipation` obtains strong terminal physical L² convergence from finite full-H³ dissipation. Thus the original sharp kinetic highpass at `rho_k=n_k+1` tends to zero along *every* cofinal sampled sequence, without a separate tightness assumption.

For selected positive strict kinetic excess and an aspect cap `sigma_k <= K rho_k`, the committed theorem `thirdFullPhysical_selectedExcess_boundedAspect_highpassFraction244` forces

```
6 E_b <= (1 + K^2) M_{rho_k}(x_k)
```

and strict excess already forces `E_b>0`. With physical highpass mass tending to zero, any fixed `K>=0` is eventually forbidden. The new theorem proves the stronger statement

```
for every fixed real K>=0:
  eventually sigma_k > K*((n_k:real)+1).
```

This is a genuine moving-*physical*-frequency rigidity result. It applies only to the natural inner radii `n+1` in the present module; arbitrarily moving real inner radii would require a separate monotonic real-cutoff comparison. It does not show that positive annular deficit snapshots exist, nor establish full H³ continuation.

## New Lean declarations

- `thirdFullPhysical_naturalSharpHighpass_sq_le_rawSpectral244`
- `thirdFullPhysical_naturalSharpHighMass_tendsto_zero_of_trace244`
- `thirdFullPhysical_finiteDissipation_naturalHighMass_tendsto_zero244`
- `thirdFullPhysical_selectedExcess_aspectEscapes_of_highMassTight244`
- `thirdFullPhysical_finiteDissipation_selectedNaturalExcess_aspectEscape244`
