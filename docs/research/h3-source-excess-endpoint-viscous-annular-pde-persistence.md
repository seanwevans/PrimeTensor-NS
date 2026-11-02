# Physical PDE persistence time for active H³ endpoint Fourier annuli

**Base:** `0256d407` — localize active H³ endpoint spikes to physical Fourier annuli.

The predecessor proves a pointwise strict annular floor on the existing selected
internal windows, and the earlier finite-band PDE polarization module proves a
**quantitative** annular dissipation variation bound from the actual projected
momentum source. This module combines those two lines of work.

Let

- `H_k = R_k² ε_k² / 8` be the selected spike threshold;
- `L_k + 1` be a proposed lower Fourier cutoff and `N_k + 1` the capture cutoff;
- `K_k = ‖S(sState_k)‖` be the attained full spectral-state maximum on the
  original source interval;
- `C_k = ‖P(sSource_k)‖` be the attained physical projected-source maximum;
- `Λ_k = h3PathFiniteAnnulusPDEVariationCoefficient244 (L_k+1) (N_k+1)
  K_k C_k` be the *actual PDE-derived* annular variation coefficient;
- `d_k = t(v_k)+w(v_k)-p_k` be the right-hand source-window space after the
  selected internal interval starts.

Whenever the selected internal endpoint window is active (`η_k>0`) and
`8 E₀ (L_k+1)^8 < H_k`, we prove the concrete new persistence time

    θ_k = min(d_k / 2, (H_k / 4) / (2 (Λ_k + 1))) > 0.

On every physical time `r ∈ [p_k,p_k+θ_k]` we have the true annular cost

    H_k / 4 < D_{<N_k+1}(r) - D_{<L_k+1}(r) ≤ D₃(r),

and the *actual Fourier annulus integral* satisfies

    θ_k (H_k/4) ≤ ∫_{p_k}^{p_k+θ_k} (D_{<N_k+1}-D_{<L_k+1}) dr.

The new interval stays inside the **same original strictly separated source
window**. It need not coincide with the prior arbitrary internal width η_k,
and θ_k does not enjoy a uniform terminal lower bound unless the actual
source ceiling, spectral envelope, capture radius, and source-window remaining
length are controlled. The four-way finite-band PDE/non-spectral/anchor/viscous
gate is retained literally.

The hypotheses do **not** include finite terminal H³ dissipation. The theorem
avoids treating H³ dissipation as uniformly continuous in time; the only
time modulus is the already proved physical projected-momentum PDE estimate
for finite-band multipliers.

## Lean declarations

- `h3Critical_scalar_annularPDE_positivePersistenceRadius`
- `h3Critical_physicalAnnulus_PDEControlledPositiveRightWindow`
- `h3Critical_sourceWindow_activeAnnularSpike_PDEPersistence`
- `h3Critical_noL2Trace_cofinalFivefold_PDEAnnularPersistenceGate`

The remaining mathematical task is summing these *new* PDE-selected annular
persistence charges, or otherwise showing their total cannot stay finite.
This requires a rate comparison between `H_k`, the true `Λ_k`, and the
remaining source-window width `d_k`. Positivity alone cannot supply it.
