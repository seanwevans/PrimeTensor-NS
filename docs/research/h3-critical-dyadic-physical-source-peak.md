# Critical H3 dyadic physical source-peak alternative

Base repository HEAD: `9450d97d2b37b8fba13def74fb270234cbdd2344`.

## Mathematical frontier

The previous accepted critical source-clock gate combines the cubic nonextension rate

    1 <= B (T-t)^8 D3(t)^3

with the *actual* physical PDE identity

    D3' + M5 + P = M3,   M5 >= 0, P >= 0.

The sharp scalar profile `D3(t)=(T-t)^(-8/3)` satisfies the first formula but
is not by itself a Navier–Stokes trajectory. The missing mathematical task is
to constrain the real Leray source `M3` in relation to `D3`, `M5` and `P`.

## New dyadic alternative

On a physical dyadic window `a < s <= t < T` with `T-s=2(T-t)`, assume that
`D3(r)>0` for `r∈[s,t]` and the cubic terminal rate holds at `t`. Define

    Q_s = log B + 8 log(T-s) + 3 log D3(s)
    C(r) = M3(r) / D3(r)

where `C` is the **actual** normalized third-radial Leray forcing mass.
For every real threshold `K`, the new dichotomy is

    8 log 2 - 3 K (t-s) <= Q_s

**or** there exists a real strict time `r∈(s,t)` such that `K<C(r)`.

The proof is not a scalar normalization. It uses the previously formalized
nonextension cubic clock, the *exact integrated PDE* identity including fifth
velocity mass and phase loss, and the physical one-sided derivative/mean-value
theorem. No independent cubic-ratio upper bound or temporal integrability
hypothesis is inserted.

A near-critical anchor with

    Q_s < 8 log 2 - 3 K (t-s)

therefore forces such an interior source peak. At that time the existing
physical Fourier norm-square identity gives

    K D3(r) < (2π)^6 Σ_{j=0}^2 ||F_{3,j}(r)||²,

where `F_{3,j}` is the actual third-radial Fourier Leray forcing component,
not an abstract test amplitude.

## Limit of the result

This is a **necessary physical alternative**, not a proof that the source
peak is impossible. To exclude a critical scalar-like physical trajectory,
the next genuinely new PDE estimate must simultaneously constrain the
normalized anchor and the attained cubic forcing peak, likely exploiting the
solenoidal Fourier triad/phase cancellations or viscous occupation of the
selected frequency band. Bounding the cubic ratio uniformly would be
stronger than what is proved here and is **not** assumed or asserted.

## Lean declarations

- `thirdFullPhysical_dyadicCubicCeiling_forces_criticalAnchorExcess244`
- `thirdFullPhysical_criticalDyadicAnchorOrActualCubicSourcePeak244`
- `thirdFullPhysical_nearCriticalAnchor_forces_actualCubicSourcePeak244`
- `thirdFullPhysical_nearCriticalAnchor_forces_thirdRadialLerayPeak244`

No `sorry`, `admit`, or new axiom. The source was statically checked, but Lean
kernel compilation must run in the user's project environment.
