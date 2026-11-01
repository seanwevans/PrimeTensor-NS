# Fivefold spectral PDE clock: actual two-endpoint H³ viscous cost

**Base:** `a8615e52` — cofinal physical source-clock or genuine high-radial temporal Fourier mass.

## Unconditional endpoint closure

Let `U(t) = h3AuditActualSpectralVelocityTotal hH3 t` be the actual weighted H³
spectral state, `D(t) = velocityH3DissipationAt u t` the actual full physical
H³ dissipation, and `H_R(t,s)` the spectral square difference outside the
Fourier ball of radius `R`.

The **already proved** `h3Critical_highTemporalMass_radiusSq_le_endpointDissipation`
establishes, at any two genuine strict physical energy-class times,

    R² H_R(t,s) ≤ 2 (D_>R(t) + D_>R(s)).

The **already proved** high-radial partition bound
`h3Critical_actualHighRadialDissipation_le_full` gives
`D_>R(t) ≤ D(t)` and `D_>R(s) ≤ D(s)`.

At each **positive** cutoff R, the previous strict high-frequency
alternative `ε² < 2 H_R(t,s)` therefore forces

    R² ε² < 4 (D(t)+D(s)),

and hence the *pointwise* alternative

    R² ε² < 8 D(t)    OR    R² ε² < 8 D(s).

The strictness in the scaled inequality uses R>0; it is not valid without
qualification at cutoff R=0. These are genuine physical endpoint quantities,
not a bound on temporal derivatives of the full H³-weighted spectral state.

## Cofinal fivefold source windows

The main theorem reuses the **same witnesses** from
`h3Critical_noL2Trace_cofinalFivefold_spectralExcursionPDEClockGate`.
At each selected source peak `t_k = t(v(k))`, write `s_k` for its attained
spectral-state maximizing time, `C_k=||R(sSource(k))||` for its *attained*
projected PDE source ceiling, and `w_k` for its original source window.

For every positive Fourier radius R and threshold ε with
`3+4 C_L ε ≤ max(1,σ(v(k)))+1`, one of these must hold:

1. One of the same accepted Riccati, compression, cutoff, spectral-anchor,
   source-anchor, source-temporal-excursion, instantaneous viscous-peak, or
   source-floor outcomes;
2. The finite-band projected-PDE clock pays
   `ε² ≤ 6 K(R) C_k² w_k²`;
3. Actual full H³ dissipation at the source peak pays
   `R² ε² < 8 D(t_k)`;
4. Actual full H³ dissipation at the attained spectral maximum pays
   `R² ε² < 8 D(s_k)`.

Here `K(R)=1+R²+R⁴+R⁶`. Exact physical A/B identities,
calibrated `δ_k`, their **pairwise disjoint** physical intervals, and the
summed full-H³ dissipation cost inequality survive unchanged.

## Important boundary

The maximizing time `s_k` belongs to the **original** interval
`[t_k,t_k+w_k]`, not necessarily to the shorter charged interval
`[t_k,t_k+δ_k]`. Therefore the new endpoint cost is pointwise and **is not
silently inserted** into the integral of dissipation over the shorter
interval. Bridging that gap needs an actual persistence or integrated
endpoint-to-window estimate. No terminal-uniform dissipation, uniform
continuity, or Navier–Stokes continuation claim follows from this theorem.

## Lean declarations

- `h3Critical_scalar_highTemporalMass_to_endpointDissipation`
- `h3Critical_scalar_endpointDissipation_forces_oneSpike`
- `h3Critical_highTemporalMass_forces_fullEndpointDissipation`
- `h3Critical_highTemporalMass_forces_onePhysicalDissipationSpike`
- `h3Critical_noL2Trace_cofinalFivefold_spectralExcursionEndpointViscousGate`

The registrar records five `#check` and five `#print axioms` entries.
Pinned local Lean/mathlib elaboration is required.
