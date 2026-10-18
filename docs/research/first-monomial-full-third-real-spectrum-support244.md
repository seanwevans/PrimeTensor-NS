# Full-third real Schwartz spectral support and coherent triads

Base checkpoint: `b36aa55f` — construct real divergence-free full-third axis Schwartz velocity.

The preceding construction gave an actual three-component *real*, divergence-free Schwartz velocity whose complexified Fourier transform exactly equals the six-window Hermitian packet. The older six-center separation result, however, applied to individual scalar windows. This module bridges that last support mismatch at the level of the **whole vector amplitude** of the actual real physical velocity.

## Mathematical content

- Identify the three reflected center pairs on `Axis Depth.three`: centers 3, 4, 5 are respectively the negatives of 0, 1, 2.
- Prove that if the three positive frequency windows vanish at both `ξ` and `-ξ`, the actual Hermitianized Fourier packet vanishes at `ξ`.
- Deduce that every nonzero spectral vector is within distance `ρ` of at least one of the six actual axis centers.
- For `0 < ρ ≤ lowNormalSixCenterSeparationRadius 1` (equal to 1/4), classify any momentum-conserving triple of nonzero vectors as a permutation of the positive triad or its reflection, and put its pair of free momenta in the corresponding product ball.
- Transport this support theorem to the Fourier transforms of the **real Schwartz velocity components**, with an explicit `WithLp.toLp` coordinate conversion.
- Define a nonnegative product of the norms of the three genuine Fourier amplitudes. Prove that it vanishes outside all twelve coherent-sector pair balls. This is a useful support majorant for later absolutely convergent trilinear integrals.
- Specialize the previously proved exact physical commutator/Fourier identification to this real, divergence-free Schwartz witness.

**Critical boundary:** This is an actual full-vector spectral support result and an exact Fourier representation for the physical witness. It does *not* identify the complete integrated seven-derivative kernel with the previously negative single-sector integral, nor does it prove a globally nonzero physical commutator. Next: express the complete symmetrized physical Fourier coefficient of this actual packet as a finite sum over twelve coherent sectors, then prove their signed sum is nonzero with the correct phase, measure and orientation factors.

## Local CI validation

Register the module, regenerate `proof/order.txt` with `python3 proof/generate_index.py`, run its `--check` and `proof/check_fragment.py --all`, compile the new module, run the theorem audit and complete `lake build`, then commit the refreshed index. This patch is statically prepared outside the Lean environment and needs local Lean compilation before its theorems are considered verified.
