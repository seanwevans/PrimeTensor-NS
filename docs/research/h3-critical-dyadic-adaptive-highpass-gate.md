# A single physical peak for every Fourier radius

Base: `7a09243738748d776ceac4848f501428821ab230`.

## Mathematical frontier

The committed H3 critical dyadic result transfers an actual physical cubic
source peak to a kinetic low-band or Leray highpass alternative at a
*prescribed* Fourier cutoff. The source peak itself is independent of that
cutoff. Therefore a stronger, operationally relevant quantifier order is
possible: **select the physical time once, and then test every radius**.

Fix a kinetic anchor `b`, a physical dyadic window `[s,t]` with `T-s=2(T-t)`,
positive top dissipation, a positive cubic coefficient `B`, the later-time
cubic rate, and a near-critical earlier anchor. The established real PDE
clock gives a strict-time witness `r in (s,t)` with

    K D3(r) < (2*pi)^6 sum_j ||F3_j(r)||_2^2.

At this same `r`, for **every** nonnegative real Fourier-gradient radius rho,

    K D3(r) < 2 (2*pi)^6 [3 L_rho + H_rho(r)],

where

    L_rho = rho^6 * volume(S_rho) * (18 rho E0(b))^2
    H_rho(r) = sum_j ||(I-P_rho)F3_j(r)||_2^2.

No order-eight raw velocity moments are assumed. In particular, whenever

    12 (2*pi)^6 L_rho <= K D3(r),

we have the quantitative genuine highpass obstruction

    K D3(r) < 4 (2*pi)^6 H_rho(r).

One of the THREE actual Fourier Leray coordinates necessarily satisfies

    K D3(r) < 12 (2*pi)^6 ||(I-P_rho)F3_j(r)||_2^2.

The coordinate may depend on rho, but **r does not**. Hence rho may be
chosen after observing the physical dissipation at r; even a state-dependent
or moving radius is covered by the same witness.

## What is not proved

This is a necessary physical concentration gate, not a new regularity proof.
Neither low frequency nor high frequency is magically excluded. An upper
estimate on the highpass *nonlinear* Leray forcing, using only natural
solenoidal H3 dynamics and viscous expenditure, remains the true new-math
obligation. The package avoids assuming exactly that missing estimate.

## Kernel audit

The new module adds four named theorems, no axioms or placeholders. The
Python registrar appends its import to `PrimeTensor.lean`, adds the import
and `#check`/`#print axioms` lines to `tools/audit/FirstMonomialTriad.lean`.
After generating `proof/order.txt`, the target and full project must be
kernel-built with the user's installed Lean/mathlib toolchain.
