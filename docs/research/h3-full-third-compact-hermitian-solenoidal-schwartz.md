# Constructing real divergence-free Schwartz velocities from compact transverse Fourier data

**Base Git HEAD:** `04c69bcf` (Hermitian complex transverse cutoff and real-solenoidal spectral bridge).

## Concrete construction

Let `χ : (Axis three → ℝ) → ℝ` be a smooth compactly supported **real** cutoff, and let `U` be a smooth, potentially non-solenoidal, complex three-component Fourier profile. Form

\[
G(\xi)=\chi(\xi)[(\xi\cdot\xi)U(\xi)-(\xi\cdot U(\xi))\xi],
\qquad H(\xi)=G(\xi)+\overline{G(-\xi)}.
\]

This does **not** divide by the origin frequency and does not require evenness or Fourier-reality of `χ` or `U`. The resulting `H` is smooth and compactly supported, Hermitian, and exactly Fourier-divergence-free. A cutoff vanishing at both `ξ` and `-ξ` produces a zero `H(ξ)`, which permits genuine origin excision by an even annular window.

Using the project's existing `thirdFullAxisHermitianize244` smoothness, support, transversality, and reality lemmas, the patch packages `H` as an actual vector Schwartz map. It then transports each coordinate along the exact `PiLp` equivalence onto `H3FourierPoint3`, takes Schwartz inverse Fourier transforms, and uses `lowNormalQuarterAxisHermitianSchwartz_fourierInv_im_zero` to obtain **real** Schwartz velocity components. Their complexified Fourier transforms recover `H` *pointwise*. Finally, `h3SchwartzDivergence_fourier` and Fourier injectivity establish actual physical spatial divergence zero at every point.

The uncorrected six-orbit / sixth-power-flux identity is then valid on all momentum-conserving triads of the **actual complex Fourier transforms of the constructed real physical Schwartz velocity**. No singularity, cancellation, or PDE continuation claim follows from that algebra alone.

## Critical limitation and next theorem

`N_ξ(U) = |ξ|² P_ξ U`, so on an annular region we must compensate this **radial factor** when approximating an arbitrary solenoidal H³ state; otherwise strong approximation does not follow. The subsequent hard theorem should:

1. Construct smooth, compact, *annular* scalar Fourier approximants with controlled weighted-H³ error.
2. Preserve Hermitian reality quantitatively, using a true contractive reflection-conjugation symmetrizer (avoid assuming arbitrary complex density is already Hermitian).
3. On the nonzero annulus choose input `U(ξ)/(2|ξ|²)` (the Hermitianization here is a sum, not an average) and apply the polynomial numerator, or use the smooth annular Leray multiplier directly; show strong convergence to the target.
4. Feed the resulting real, physical solenoidal Schwartz velocities into the existing **exact zeroth-, second-, and third-derivative jet** bridges to obtain the matched canonical H³ limit without inserting an approximation axiom.

This patch delivers the **constructive realization** for every compact-smooth input and makes the quantitative density obligation explicit, rather than conflating it with projection at the abstract `L²` level.

## Acceptance

- `python3 tools/audit/register_h3_full_third_compact_hermitian_solenoidal_schwartz.py --apply`
- `python3 proof/generate_index.py` and `--check`
- `lake env lean PrimeTensor/Fluid/Vorticity/Continuation/H3/Critical/Transport/FullThirdCompactHermitianSolenoidalSchwartz.lean`
- `lake build PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdCompactHermitianSolenoidalSchwartz`
- `python3 proof/check_fragment.py --all` then `lake build`

The patch is not locally Lean-compiled: this environment does not contain `lean` or `lake`.
