# Exact radial Plancherel transfer of projected-PDE time increments

Base commit: `6ba8f6d3` — derive physical L2 momentum temporal modulus from projected PDE.

The `FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalKineticProjectedSourceSpectralFiniteAnnulusPDEFourierTransfer244.lean` module reuses, rather than reproves, the exact weighted Fourier cutoff theorem
`weightedSpectralVelocityRadialSquareDefect_le_ceiling_mul_rawVelocityFourierTotalSquareDefect` from the project's *physical dissipation bounded radial weighted Cauchy* development.

Let `S(t)` be the actual weighted H³ spectral state, `U(t)` the old physical L² Hilbert velocity, and
`K(ρ) = h3TerminalRadialSobolevWeightSquareCeiling ρ = 1+ρ²+ρ⁴+ρ⁶`.
Plancherel and the exact physical three-coordinate jets give the generous but safe estimate

    ∫_{|D|<ρ} Σ_j |S_j(s,ξ)-S_j(t,ξ)|² dξ
      ≤ 3 K(ρ) ‖U(s)-U(t)‖².

This contains the precise real/complex Fourier normalization; no independent physical/spectral identification is assumed. Combining with the strong physical projected-PDE derivative from the old-pressure distributional FTC yields, when `‖R(r)‖₂≤C` on `[s,t]`,

    WeightedRadialDefect_ρ(S(s),S(t)) ≤ 3 K(ρ) C² (t-s)².

The exact reconstructed Laplacian-minus-Leray bound `‖R(r)‖₂≤(3+C_Leray) E₃(r)` converts any local H³-energy ceiling `E` into the coefficient `C=(3+C_Leray)E`. Continuity of the projected source supplies `C` on any compact strict-preterminal interval.

These are conditional only on the existing `LoggedPreterminalH3PathAdmissible` (and explicitly stated positive intervals). The bounds are quantitative **for a fixed cutoff and a strict subinterval** but their coefficients can diverge as the cutoff or terminal time increases. They do not furnish a global H³ time derivative, fourth-order dissipation continuity, uniform terminal width, or the Navier–Stokes regularity conclusion.

## Next analytical step

Apply the cutoff gradient multiplier to the radial weighted difference. For any cutoff `ρ`,

    Σ_j ‖1_{|D|<ρ}|D|(S_j(t)-S_j(s))‖²
       ≤ ρ² RadialWeightedDefect_ρ(S(t),S(s)).

Then polarization of the cutoff multiplier squared norms yields an *explicit finite-annulus dissipation variation modulus* with the PDE source ceiling replacing the abstract spectral rate `V` in the preceding quantitative-window theorem. The sharp issue at terminal escape remains how `ρ`, the outer cutoff, and `C` scale with n relative to the cubic height.
