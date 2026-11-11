# Critical H³ highpass forcing: exact Young gap and sharpness obstruction

Pinned source HEAD: `516228b36f4568ee29668f989171985679c52777`.

## Why this audit matters

The accepted physical Fourier chain has converted highpass H³ forcing into
viscous fifth mass and the **signed** phase defect, and phase into actual
fourth-radial temporal expenditure. The previous source bound carried a
coefficient of 2, which might tempt a formal absorption if thought to be a
slack artifact. It is in fact **sharp for a single Fourier coordinate**.

For q >= 0, z, f complex, denote

    M5 = q^5 |z|^2,
    M3 = q^3 |f|^2,
    Phase = q^3 |q*z+f|^2.

The Hilbert parallelogram identity gives the exact equality

    2*M5 + 2*Phase = M3 + q^3 |f + 2*q*z|^2.

The previous `M3 <= 2*(M5+Phase)` was obtained by discarding exactly
this last positive square, not by a merely nonoptimal Young inequality.

## Saturation and the scalar obstruction to absorption

For every q>0, equality holds if and only if `f = -2*q*z`. At the
explicit mode `q=1, z=1, f=-2`:

    M5 = 1, Phase = 1, M3 = 4, M3-M5-Phase = +2.

Consequently NO coefficient C<2 can give `M3 <= C*(M5+Phase)` over all
complex Fourier coordinates. This is an algebraic statement, **not an
assertion that this mode is realized by a real-solenoidal physical
Navier--Stokes solution**. Indeed, the exact fourth-radial Fourier PDE
in the accepted module would give its temporal residual an anti-diffusive
sign at that isolated mode. Realizable triad interactions must be tested.

## Physical spectral rigidity defect

The exact gap identity is valid after integrating over any measurable
Fourier band for which the physical fifth, cubic, and phase densities are
integrable. Those hypotheses have already been proved at strict physical
times. A new coordinate theorem installs the identity at the actual sharp
highpass for the physical Leray nonlinear source and velocity. No sixth
velocity moment, terminal-uniform control, or invented regularity is used.

The next hard-math task is **not another algebraic absorption of the same
three masses**. It is to determine whether the real-solenoidal triad
constraints and kinetic-energy flux orthogonality force a quantitative
lower bound on the integrated gap, or otherwise prevent persistent
near-saturation on critical terminal windows.

The exact algebraic gap and its scalar saturation do **not** by themselves
prove an a priori H³ estimate or Clay Form A.

## Declarations

- `thirdFullKinetic_complexParallelogramGap244`
- `thirdFullKinetic_cubicFifthPhase_exactGap244`
- `thirdFullKinetic_cubicFifthPhase_saturation_iff244`
- `thirdFullKinetic_fifthPhase_factorTwo_optimal244`
- `thirdFullKinetic_bandCubicFifthPhase_exactGap244`
- `thirdFullPhysical_highCubicFifthPhase_exactGap_coordinate244`
