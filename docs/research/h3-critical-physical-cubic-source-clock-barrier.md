# Critical cubic physical source clock: the 8/3 frontier

Base repository HEAD: `df887ce58bedde9ba627dbbd2ca9973e1ad57658`.

The accepted scalar sharpness model `D(d)=d^(-8/3)` shows that the
pointwise cubic blow-up rate alone cannot exclude a physical singularity.
The next constraint must use Navier–Stokes dynamics.

For an actual H³ energy-class path with positive top-third dissipation,
the already kernel-proved physical PDE gives the exact normalized balance

    ∫_s^t M3/D3 = log(D3(t)/D3(s)) + ∫_s^t (M5+P)/D3,

where `M3` is the actual third-radial Leray forcing mass, `M5` is actual
fifth-radial velocity expenditure, and `P>=0` is physical phase mismatch.
The compact-time integrability of the combined expenditure is automatic in
`h3Path_topJointAction_eq_cubic_sub_log_automatic244`.

If the terminal cubic nonextension rate holds at `t`,

    1 <= B (T-t)^8 D3(t)^3,  B>0,

then taking logarithms and combining with the PDE identity yields

    8 log((T-s)/(T-t))
      <= 3 [∫_s^t M3/D3 - ∫_s^t (M5+P)/D3]
         + log(B (T-s)^8 D3(s)^3).

For a last-half clock with `T-s = 2(T-t)`, the left side is `8 log 2`.
This is a rigorous *necessary physical source clock*, with its actual
fifth/phase losses preserved. A source action deficit strictly below that
threshold contradicts the cubic rate. The displayed deficit has NOT been
proven for arbitrary Navier–Stokes solutions.

## Frontier

The open hard-math step is an independent, PDE-derived **upper** estimate on
the normalized signed net physical cubic clock. In particular, an upper
estimate with asymptotic log slope strictly less than `8/3`, while retaining
control of the fifth/phase term and anchor offset, would contradict the
nonextension cubic rate. Merely recombining the cubic lower bound does not
prove such an estimate. The result should therefore be read as a precise
frontier gate, not as an unconditional continuation theorem.

## New Lean declarations

- `thirdFullPhysical_criticalCubicRate_forces_actualSourceClock244`
- `thirdFullPhysical_actualSourceClock_deficit_excludesCriticalCubicRate244`
- `thirdFullPhysical_criticalCubicRate_forces_dyadicSourceCharge244`

No new axioms or proof placeholders. Kernel verification is required locally.
