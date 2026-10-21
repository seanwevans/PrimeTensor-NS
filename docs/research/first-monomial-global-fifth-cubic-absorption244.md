# Signed global fifth-radial absorption by cubic Leray forcing

Base commit: `6227cb9b`, *bound global absolute Leray transfer by fifth velocity and cubic forcing masses*.

## PDE signs and exact bridge

The physical global fourth-radial pairing equals `Heat5 + Leray5`, where `Heat5 = -2 M5`. The earlier terminal transfer program proves `TailLeray(R) <= G` for every real radial cutoff. At `R=0` the low-frequency strict sublevel is empty, so `TailLeray(0) = Leray5` literally, without a frequency limit. The previous checkpoint proved `G <= M5 + M3` from a weighted Fourier Young square, with `M5` the unrestricted fifth velocity square moment and `M3` the cubic Leray-forcing square moment. Therefore

    D3'(t) + M5(t) <= M3(t).

This is a genuine *signed*, coercive inequality for the physical fourth-radial dissipation derivative, not an inequality for the absolute value of that derivative. It retains one entire fifth-moment dissipation share.

## Quantitative alternatives

- `M3 <= M5` implies `D3' <= 0`.
- `D3' > 0` implies `M3 > M5`.
- `M3 <= θ M5` implies `D3' <= -(1-θ) M5`.
- With `θ < 1` and `M5 > 0`, that derivative is strictly negative.

No terminal-uniform forcing fraction or integrability assumption is asserted. Critically, normalized spectral variance has derivative `-X/(E0 D3)^2`; the term `D3'` enters `X` with a negative sign, so this coercive *upper* bound on `D3'` does not itself bound concentration production from above. Attempting that substitution would reverse the inequality and be invalid. A genuinely new signed relationship involving the middle moment or normalized rate remains necessary for unconditional regularity.

## Audit

The registrar adds the module import to `PrimeTensor.lean` and the central first-monomial audit, plus `#check` and `#print axioms` for eight new theorems. Run `proof/generate_index.py`, the fragment audit, local/full builds, and baseline before pushing.
