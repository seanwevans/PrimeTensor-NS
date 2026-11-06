# Late viscous source-state quintic physical barrier

Base: `a5788f52c183fa9d5f12d9dffd740df1f8b02622`.

This is a necessary condition for failure of an H3 terminal trace, not a proof of continuation.

The actual low-radial projected-PDE rate on a finite radial cutoff J, with
attained H3-weighted state maximum K and projected momentum source maximum C, has

    Lambda_J <= 24 K C (J+2)^5.

The proved existing rate-versus-compression gate says, for the normalized
prescribed-gauge spike A = H(v(k))^4/(2P_k) and true terminal viscous integral
B = integral_{m(k)}^T D_H3,

    (T-r(k)) A <= 4B or A^2 <= 2 (Lambda_J+1) B.

Since B>=0, the second case splits into

    A^2 <= 4B or A^2 <= 96 K C (J+2)^5 B.

Thus the same first-crossing gauge-dependent windows and finite disjoint viscous
costs yield an explicit terminal physical alternative: Fourier terminal carrier,
early attained actual source peak, kinetic clock, remaining-time compression,
small normalized spike relative to true tail dissipation, or an actual
state-times-source fifth-cutoff payment. The last two cases are both refinements
of the former late PDE-rate branch.

No bound on the moving radial capture cutoff, strict-time source, strict-time
weighted spectral state, or terminal time compression is assumed or proved.

New declarations:
- `thirdFull_lateLowRadialPDERate_le_quinticPhysicalProduct244`
- `thirdFull_scalar_lateRate_quinticProductOrTail244`
- `thirdFullPhysical_noH3Trace_prescribedGauge_lateQuinticProductOrCompression244`
