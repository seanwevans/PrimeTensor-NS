# Canonical projected PDE source: quantitative physical spectral difference

Parent checkpoint: `6e5e2085` (`bound raw Leray Fourier differences and isolate canonical spectral temporal displacement`).

## Mathematical statement

For the actual weighted three-dimensional spectral velocity states U,V, the inverse Fourier real physical reconstruction has exact subtraction functoriality. The preexisting raw Fourier estimate yields

`‖L(U)-L(V)‖_L² ≤ C_L(‖U‖+‖V‖)‖U-V‖`,

where `C_L = 3 * (576 * π * h3SobolevDeweightingConstant)` is the calibrated physical nonlinear coefficient. The physical Laplacian is linear and satisfies `‖D(U)-D(V)‖_L² ≤ 3‖U-V‖`. Therefore the **actual physical inverse-Fourier projected momentum source** has

`‖(D(U)-L(U))-(D(V)-L(V))‖_L² ≤ (3+C_L(‖U‖+‖V‖))‖U-V‖`.

The strict positive-time source is defined by those exact physical Fourier reconstructions; no standalone source temporal modulus, bounded state, or terminal trace has been introduced.

## Terminal clocks

The package preserves the original canonical attained source maxima `s(k)` in `[τ(v(k)), (τ(v(k))+T)/2]` and original exact quadratic-sharp dissipation windows anchored at `τ(v(k))`. Their physical source temporal increment is thus bounded by the actual weighted spectral-state displacement times the displayed amplitude-dependent factor. The previously proved conditional critical-width spectral anchor/displacement alternatives apply to the same witnesses.

Crucial limit: finite full H³ time-integrated dissipation **alone does not bound** the spectral time increments or state amplitudes on half-terminal source windows. The geometric noncompression, sixth-order linear-rate and ninth/eighth-width conditions remain explicit.

Proof status: generated Lean source, not compiled in the assistant runtime; local `lake env lean` and `lake build` are required.
