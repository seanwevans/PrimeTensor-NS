# Signed global radial heat barycenter and two-band obstruction

Base: `8e003dc9`, *couple normalized middle Fourier evolution to signed fifth cubic phase defect*.

## Physical heat factorization

Set `m0=E0`, `m1=D0`, `m2=E2`, `m3=D2`, `m4=D3` and `m5=M5`. These are actual nonnegative physical Fourier moments on a strict H3 time slice. The established diffusion integration-by-parts identities imply `L0=-2m1` and `L2=-2m3`; the global heat identity gives `Heat5=-2m5`.

The normalized HEAT contribution is exactly

    B_heat = 2 m2 [m2(m1 m4 + m0 m5) - 2m0 m3 m4] / (m0 m4)^2.

For positive `m0,m2,m4`, its sign is the sign of the weighted barycenter imbalance

    m1/m0 + m5/m4 - 2m3/m2.

The factorization theorem is established in the physical energy class; no PDE approximation, terminal assumption, or Fourier cutoff enters it.

## Two-band counterexample to a HEAT sign shortcut

Take the algebraic spectral model with mass `x` at `q=1` and mass `y` at `q=2`. Its six moment values are `m0=x+y`, `m1=x+2y`, `m2=x+4y`, `m3=x+8y`, `m4=x+16y`, `m5=x+32y`. The unnormalized numerator is

    18xy(x-4y)(x+4y).

For `x,y>0` this switches sign at `x=4y`. At `(x,y)=(8,1)` the normalized signed heat source equals `4/27 > 0`; at `(1,1)` it equals `-135/578 < 0`; at `(4,1)` it is zero. These finite-band measures are diagnostic algebraic spectral data, not themselves smooth Navier-Stokes solutions. They show that positivity of each heat dissipation moment is insufficient, as a matter of algebra, to prove a universal sign for normalized variance heat production.

## Consequence for the ongoing program

The signed top-phase term `M5+P-M3` and the middle diffusion coupling must be controlled jointly, or supplemented with genuinely new spectral localization/cancellation information. A proof claiming pure heat always destroys (or always creates) normalized spectral concentration would be false even in this elementary two-band moment model. This checkpoint does not give an unconditional regularity or terminal anti-concentration theorem.
