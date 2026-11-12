# Actual nonlinear annular Young residual: strong Fourier L² continuity

Base: `1084b481d2b09847883f2d7fc2ba01264e1a8bd3` (`derive actual annular highpass continuity and one-snapshot deficit viscous windows`).

## Hard mathematical advance

The exact Young-gap residual in the previously accepted annular deficit is **not** an arbitrary local surrogate. Let `U(t)` be the actual weighted H³ spectral velocity, `N_j(U,U)` its genuine quadratic Leray Fourier convolution, and `L_j(U) = -q z_j` the actual Fourier Laplacian, where `q(ξ)=(2π)²|ξ|²`. The residual

    G_j(U) = N_j(U,U) - 2 L_j(U)

has the same almost-everywhere Fourier representative as `N_j(U,U)+2q z_j` in the original physical Young-gap/width integral.

The already established bilinear Fourier L² difference estimate and the contractive weighted-H³-to-Fourier-L² Laplacian yield

    ||G_j(U)-G_j(V)||₂
       <= [576 π C₃ (||U||_{H³}+||V||_{H³}) + 2] ||U-V||_{H³}.

This is a direct locally Lipschitz estimate of the **actual nonlinear residual**. No full-H³ norm ceiling, global time modulus, or dissipation-square estimate is added as a premise.

For a fixed ordered pair `rho<=sigma`, let `P_r` be the established norm-one sharp Fourier lowpass. The new operator `(P_sigma-P_rho) G_j(U)` is continuous on the weighted H³ Hilbert state, and therefore along every strictly positive physical path. Its a.e. representative is exactly the sharp annulus indicator multiplied by `G_j(U)`. Plancherel identifies its square norm with the unweighted, **genuine nonlinear Fourier Young-residual integral**

    ||(P_sigma-P_rho) G_j(U(t))||₂²
      = integral_{rho<=2π|ξ|<sigma} |N_j(U(t),U(t)) + 2q(ξ) z_j(t,ξ)|² dξ,

which is consequently continuous at each strict time. The endpoint convention follows the exact pre-existing sharp cutoff definition.

## Exact remaining formalization gap

The physical Young-width cost of `AnnularDeficitPersistence.lean` contains `q(ξ)^3` inside the first integral, in addition to the separately weighted velocity mass. On the fixed annulus, `0<=q<=sigma²` when `0<=rho<=sigma`. Therefore **mathematically** the bounded multiplier

    f ↦ 1_{A_{rho,sigma}} q^{3/2} f

is continuous on Fourier L², with operator norm at most `sigma³`. Applying it to the strongly continuous `G_j(U(t))` proves continuity of the exact q³-weighted Young residual by the L² norm-square identity. The second frequency-width term follows from continuity of the raw Fourier velocity L² state and the same sharp annular projector.

However, **the present Lean file proves only the unweighted integral continuity**, not the bounded cubic multiplier construction or its q³-weighted norm-square equality. The latter must be formalized before removing the `hYoung` premise from `thirdFullPhysical_annularDeficit_snapshotRightWindowCharge244`. Merely bounding the weighted integral by `sigma^6` times the unweighted one is insufficient to establish temporal continuity; the actual multiplier continuity and equality are required.

Even after the fixed-radius continuity gap is closed, the constants can grow with moving `sigma_k` and the spectral norm on each preterminal slab. No uniform cofinal positive-window width, no contradictory diverging viscous clock, and no terminal H³ continuation follow at this stage.

## Verification boundary

The registrar rejects unproved placeholders and registers each theorem for `#check` and `#print axioms`. Source screening is distinct from Lean kernel compilation. Execute the ZIP and script on the pinned Lean/mathlib environment and require all Lean builds and audits to pass before any commit.
