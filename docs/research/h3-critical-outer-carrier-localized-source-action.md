# Highpass-localized source action and signed Young residual

Base commit `1d1482eb5` (*reduce selected outer signed source payment to two-radius quartic cost*).

## Actual Navier–Stokes momentum action

For the genuine old physical L² Hilbert velocity `U(t)`, write `P_ρ = I − sharpLow_ρ`, the previously proved nonexpansive highpass. The unconditional physical momentum FTC gives `U(s) − U(x) = ∫ₓˢ F(t) dt` where `F` is the actual projected Navier–Stokes momentum source. Thus

```
S_ρ(x,s) := ‖P_ρ (∫ₓˢ F(t) dt)‖
           = ‖P_ρ U(s) − P_ρ U(x)‖
           ≤ ∫ₓˢ ‖F(t)‖ dt.
```

No claim about commuting `P_ρ` with the Bochner integral is required. The time-integrated source itself is projected. This is sharper than the full action because of spatial-frequency and time cancellation.

The actual highpass kinetic mass `M(t)=‖P_ρ U(t)‖²` therefore satisfies the **fitted** difference bound

```
|M(s)−M(x)| ≤ S_ρ(x,s) [2 sqrt(M(x)) + S_ρ(x,s)].
```

## Signed Young residual

The prior exact early-anchored annular identity and the positive-deficit signed-polarization lemma give

```
G(x)−G(s) ≤ 2 ρ^6 σ^4 M(x) |M(x)−M(s)|
                     + M(s) [Y(s)−Y(x)].
```

Hence a selected deficit drop `G(x)-G(s)>ε` implies the *full*, factor-of-two-free residual

```
ε − 2ρ^6 σ^4 M(x) S_ρ(x,s)[2 sqrt(M(x))+S_ρ(x,s)]
  < M(s)[Y(s)−Y(x)].
```

If `Y(s)≤Y(x)`, the complete positive deficit drop must be paid by the localized physical source. When additionally `S_ρ(x,s)≤sqrt(M(x))`, this sharpens to

```
ε < 6 ρ^6 σ^4 M(x)^(3/2) S_ρ(x,s).
```

This **cubic highpass-amplitude cost** is tighter than the previous coefficient proportional to the *total* physical L² kinetic energy.

## Terminal conclusion and open analytic work

Since `P_ρ` is a contraction, for *arbitrary moving cutoffs* `ρ_k` and subwindow endpoints `x_k≤s_k<T` with `x_k→T`, finite physical H³ dissipation and the already proved kinetic-anchor source-integrability theorem imply `S_{ρ_k}(x_k,s_k)→0`.

This is an unconditional consequence under the established `PreterminalH3EnergyClass` and finite-dissipation hypotheses, **not** a bound on the weighted product `ρ_k^6 σ_k^4 M_k(x_k) S_k(2 sqrt(M_k(x_k))+S_k)`.

The next genuine frontier is to control this frequency-weighted highpass source action using the signed Fourier triad structure or the physical viscous spectral channel. Without that estimate there is no H³ continuation contradiction.

## Formal proof inventory

The module declares 12 Lean theorems and 2 definitions: exact localized physical FTC, contraction, fitted quadratic mass drift, exact selected mass slope cap, signed Young residual, no-growth source payment, cubic highpass amplitude payment, half-terminal residual, uniform terminal-source domination, cofinal localized action decay and cofinal localized Young alternative. No additional axioms or proof placeholders are introduced. These source proofs are not Lean-compiled in the packaging environment; the guarded script performs the required build.
