# Second-generation late-viscous squared-tail barrier

**Base:** `a66302df9a5cbfe6c5bf6dd3a92036796276abc6` — accepted constructive reciprocal-square-root terminal-tail and secondary spectral cutoff cost.

## Mechanism

On the constructive late-viscous branch, put

- `A = H(vk)^4 / (2 P) > 0` — normalized prescribed-gauge fourth-power amplitude;
- `B = integral_(m)^T D_H3(t) dt > 0` — actual full H3 viscous action;
- `R = 96 (3+C_L) (J+2)^5 > 0` — the first finite-band physical rate multiplier;
- `h = A / (12 sqrt(R B)) > 0` — constructive secondary viscous height.

The preceding theorem selects an *actual* time `s` among the attained state/source maxima, finite cutoff `J2`, and attained second-window source/state maxima `C2,K2`, together with

```
eta2 = min ((T-s)/4) ((h/2)/(2*(Lambda2+1))) > 0,
eta2 * (h/2) <= B,
Lambda2 <= 24 K2 C2 (J2+2)^5.
```

Eliminating this second PDE clock via the existing verified rate-or-compression and physical quintic splitting lemmas gives

```
(T-s)*(h/2) <= 4B
or (h/2)^2 <= 4B
or (h/2)^2 <= 96 K2 C2 (J2+2)^5 B.
```

Since `h/2 = A/(24 sqrt(R B))`, the *positive* scale factor `576 R B` yields

```
(T-s)*A <= 96 B sqrt(R B)
or A^2 <= 2304 R B^2
or A^2 <= 55296 R K2 C2 (J2+2)^5 B^2.
```

The last two arms have a **squared actual terminal H3 dissipation action**. This is not an independently summed charge: both first and second windows may overlap, but only the second window's previously verified local integral and clock are used here. The strengthened cofinal theorem retains the same `U, tau, N, K, C, delta, v` and the same frequency escape and finite original disjoint charge sums; its new conditional output supplies this additional physical budget in the constructive late branch.

## What this does not prove

Neither cutoff `J2` nor the actual maxima `K2,C2` have a terminal-uniform bound. Time compression `(T-s)*A` may also be small. Consequently finite tail action alone does not exclude the new alternatives and no continuation claim follows. The remaining hard step is to quantitatively constrain the second-generation rate/temporal compression using physical signed H3 transport, rather than summing overlapping positive windows.

The registrar checks all declarations and axiom lists, enforces no proof placeholders, and checks idempotence. Elaboration against the pinned Lean/mathlib toolchain is required on the host.
