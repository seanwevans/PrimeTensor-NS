# Initial physical zeroth-order L² trace to actual H³ spectral right trace

Parent: `31fa84c8` (`derive initial weak H3 correlation from physical raw L2 trace`).

## What is new

The former right-trace interface assumed convergence of three raw Fourier `L²` states to a separately chosen weighted H³ spectral initial datum `U₀`. This module defines the actual **physical** zeroth-order `L²` velocity jet on `(0,T)` and obtains the raw Fourier limit by the project's unitary scalar Fourier transform.

The datum `U₀` is now obtained from the **actual t=0 velocity H³ encoder**. The existing exact energy identity `1 + spectralSquareEnergy(U₀) = velocityH3EnergyAt u 0` eliminates the separately chosen spectral energy normalization. A one-sided energy upper bound relative to the actual physical initial H³ energy then supplies the previous upper-envelope interface. The optional spatial-C³ version proves initial Fourier compatibility from a physical regularity assumption.

The resulting theorem passes through the previous weak-correlation and one-sided polarization bridges and gives the initial actual physical H³ strong trace, then the conditional full-time `L²_t Ḣ^(3/2)_x` estimate for both transverse velocity components.

## What remains explicitly assumed

1. The actual t=0 velocity is H³ integrable, measurable, and Fourier-compatible (or has spatial C³ in the alternate contract).
2. The three real-valued **physical-space zeroth-order velocity L² jets** converge as `t -> 0+` to the t=0 physical L² jets.
3. The physical H³ energy satisfies an initial right limsup inequality relative to the actual `velocityH3EnergyAt u 0`.
4. The terminal actual vorticity strong-H³ endpoint, energy class and Liu–Zhang external continuation implication are not discharged by this module.

No global Navier–Stokes regularity or existence theorem is claimed. The new file contains no `sorry`, `admit`, or new axiom declarations. It has not been compiled in the patch authoring environment.
