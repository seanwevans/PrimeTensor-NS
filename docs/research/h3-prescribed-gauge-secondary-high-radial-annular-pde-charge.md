# PDE-controlled finite-annulus temporal charge at the original secondary H³ observations

**Base:** `30576becb2d257adf250d2449245a40f3d1487d8`.

## New analytical bridge

The preceding cofinal theorem supplies, under its activated deep-excess rate and
noncompressed primary clock, actual secondary times `zState`, `zSource` and a
cutoff `J₂` at which the high-radial H³ viscous dissipation must exceed a
threshold. This module does NOT reselect either original secondary time.

For fixed `σ ≥ 0`, `M > 0`, if `D_high,σ(x) > 2M` at one such time `x`,
then pointwise convergence of the outer H³ dissipation tail at that same
strict time selects a finite cutoff `Q = N+1` with `D_high,Q(x) < M/2`.
The exact radial partition yields a physical FINITE annulus with

    D_[σ,Q](x) = D_high,σ(x) - D_high,Q(x) > 3 M/2 > M.

Fix the compact forward half-tail `d=(T-x)/2`. The existing actual attained
source/state maximum theorem supplies finite `C` and `K` on `[x,x+d]`:

    C = ||projectedPhysicalSource(qSource)||,
    K = ||actualWeightedSpectralState(qState)||.

The previously proved *real physical Navier--Stokes* annular variation theorem
gives the certified persistence width

    Lambda = h3PathFiniteAnnulusPDEVariationCoefficient244 σ Q K C,
    delta = min (d/2) ((M/2)/(2*(Lambda+1))) > 0.

On the ACTUAL selected subinterval `[x,x+delta]`:

    M/2 < D_[σ,Q](r) <= D_H3(r),
    delta * M/2 <= integral_x^(x+delta) D_[σ,Q](r) dr
                 <= integral_m^T D_H3(r) dr.

The last inequality uses the already assumed interval-integrability of actual
full fourth-derivative dissipation and contains no new dissipation budget.
The theorem `thirdFullPhysical_secondaryTwoSlice_forcesAnnularPDECharge244`
instantiates the same original squared-tail physical two-slice gate; the
higher demand threshold uses `Lσ + 2M` so that the finite annulus can retain
`M/2` on the PDE clock. The source/state maxima on the compact forward
interval are only auxiliary **rate coefficients**, not new spike times.

## Still open

This creates a physical positive-width, explicitly rate-controlled annular
charge, but neither bounds the moving outer cutoff `N` nor the attained rate
`Lambda`. In particular `delta * M/2 <= B` is compatible with `B -> 0` when
`delta` shrinks rapidly. The newly selected intervals may overlap previously
charged windows and must not be added to their sums without a disjointness
argument. The next hard problem is a scale-independent constraint on the
moving cutoffs/rates, or an independent compression contradiction.

The proof must be compiled using the repository's pinned Lean 4.34.0-rc1
and mathlib toolchain. No `sorry`, `admit`, or new axioms are intended.
