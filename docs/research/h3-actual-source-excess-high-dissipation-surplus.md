# Actual Fourier source excess yields physical H³ dissipation surplus

Base checkpoint `695217ee`: square-root calibrated source-peak physical quartic clock.

## New quantitative coercivity

Let `H_{rho,i}(t)` be the genuine highpass Fourier representation of the projected
physical momentum source. Write `E0` for kinetic energy at the strict anchor `b`,
`D_hi` for actual high-radial physical H³ dissipation above `sigma`, and

    K0 = 3 + C_L > 0
    L = sigma² * W₃(sigma) * E0
    B(sigma,M) = max(K0*(1+6E0+3*(L+M)),0).

The previously proven physical Fourier-source majorant is

    ||H_{rho,i}(t)|| <= K0 * (1+6E0+3*(L+D_hi(t))).

Because `B(sigma,M)` is at least the same expression with `D_hi` replaced by
`M`, subtraction yields the new *exact pointwise quantitative* estimate

    ||H_{rho,i}(t)|| - B(sigma,M)
       <= 3 K0 (D_hi(t)-M).

Consequently, if the actual source exceeds `B(sigma,M)+Q`, then

    D_hi(t) > M + Q/(3 K0).

This is a physical same-time estimate with no terminal-uniform energy ceiling
and no Fourier state proxy. Its coefficient is independent of the source
and dissipation cutoff radii. No sign condition on M is required for the
pointwise subtraction; the cofinal cost construction takes nonnegative M,Q.

## Cofinal enhanced source/excess windows

The existing no-strong-terminal-L²-trace source-driven theorem accepts *any*
square highpass Fourier-source floor. Select the floor

    Ksource(n) = [B(sigma(n),M(n))+Q(n)]²

for an arbitrary nonnegative extra source-excess profile `Q(n)`. The existing
Plancherel highpass identity implies that on the resulting cofinal, separated
windows, *for every physical time* s:

    ||H_{rho(n),i}(s)|| > B(sigma(n),M(n)) + Q(n),
    D_>sigma(n)(s) > M(n) + Q(n)/(3K0).

Since actual full physical H³ dissipation bounds the high-radial part, the
full extended Lebesgue dissipation charges satisfy, for every finite m,

    Σ_{k<m} ofReal(M(vk)+Q(vk)/(3K0)) * ofReal(delta(vk))
      <= Σ_{k<m} ∫⁻_(t(vk),t(vk)+delta(vk)] ofReal(D_full(s)) ds.

This strengthens the previously qualitative threshold M to an explicitly
source-excess driven surplus. The time windows may shrink arbitrarily;
this does not prove divergence of the weighted costs or global continuation.

Lean declarations:
- `h3Critical_actualHighpassSourceExcess_le_highRadialDissipationSurplus`
- `h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus`
- `h3Critical_sourceMassExcess_forces_quantitativeHighRadialSurplus`
- `h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts`

Validate with the pinned Lean/mathlib environment. Static checks are not proof elaboration.
