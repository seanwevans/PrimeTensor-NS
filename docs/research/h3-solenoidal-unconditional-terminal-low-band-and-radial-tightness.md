# Actual solenoidal H³ terminal low-band limits and sharp radial-tightness alternative

Base HEAD: `0e0c7703dd54dc17888a0334ba69c6ccbe80f8f4`.

## Unconditional positive-time physical FTC

`h3Path_physicalHilbertFTC_betweenPositiveTimes244` already proves the exact old-branch Bochner momentum evolution identity directly from `LoggedPreterminalH3PathAdmissible`. The earlier conditional `thirdFullActualLowBandFourierVector_strictFTC_of_oldJoint244` therefore had an avoidable additional temporal-joint-continuity assumption. The new `thirdFullActualLowBandFourierVector_strictFTC244` composes the existing unconditional Hilbert FTC with the genuine finite-band physical Fourier continuous linear map, commuting it with Bochner time integration. It is an interface improvement, not an independent derivation of the old-pressure/curl weak evolution used deeper in the dependency chain.

## Fixed-band terminal Cauchy without kinetic trace

For any strict interior anchor `b ∈ (a,T)` and every natural cutoff `R`, physical low-pass momentum source integrability on `(b,T)` implies a Cauchy modulus for the Fourier-localized physical velocity. The exact bounded Sobolev weight on the band transfers it to the genuine weighted H³ spectral state. Thus

`ThirdFullTerminalLowRadialCauchyOn244 (h3AuditActualSpectralVelocityTotal hH3) b T`

is proved with *only* the logged H³ path and preterminal energy-class hypotheses, not an old-joint continuity condition or full kinetic Cauchy hypothesis. Completeness produces a strong terminal limit for each fixed projected low band.

## Exact terminal radial-tightness equivalence

If `P_R` denotes the existing high-radial Fourier projection and `U(t)` the actual H³ spectral state, then

* a terminal H³ trace entails endpoint-uniform `P_R` tightness via `‖P_R(U(t))‖ ≤ ‖U(t)-L‖ + ‖P_R L‖`;
* endpoint-uniform `P_R` tightness plus the now automatic low-band Cauchy property yields a full H³ trace.

Hence these two conditions are equivalent for the actual path. Negating either yields an exact cofinal escape alternative, with one positive ε selected before every natural cutoff R and terminal width δ.

This is a **criterion**, not proof of endpoint high-frequency tightness. It neither establishes a terminal H³ trace unconditionally nor resolves Navier–Stokes continuation. The next difficult PDE step is to rule out persistent, cofinal high-frequency escape using the physical spectral/viscous budget, without converting finite interior H³ continuity into an unjustified endpoint-uniform estimate.

## Local verification

Static declaration, registration and archive integrity checks pass. No Lean executable or complete repository/toolchain is available in this container; Lean and full-project audit must run in the user's repository.
