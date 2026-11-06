# Physical kinetic-anchor and two-slice late viscous rate gate

**Base:** `602677fa3f81da41f3c139997798be169bcaa60a`.

The accepted prescribed-gauge fifth-order source-state rate charge on the delayed
half-terminal branch contains the actual (attained) product
`K = ‖h3AuditActualSpectralVelocityTotal hH3 sState‖` and
`C = ‖h3PathActualProjectedMomentumSource244 hH3 sSource‖`.

The existing physical spectral-energy comparison and kinetic-tail estimate yield
`K² ≤ E_H3(sState)`, `1 ≤ E_H3(sState)` and
`E_H3(sState) ≤ E_b + 3 D_H3(sState)`, whence
`K ≤ E_b + 3 D_H3(sState)`. The existing pointwise projected-source estimate
supplies `C ≤ (3 + C_L)(E_b + 3 D_H3(sSource))`.
Here `E_b = 1 + 6 E_0(b)`. Both times belong strictly to `(b,T)`.

Consequently the late rate branch becomes the exact physical necessary condition

```
A² ≤ 96 (3+C_L) (E_b+3D_H3(sState)) (E_b+3D_H3(sSource)) (J+2)^5 B
```

where `A=H(vk)^4/(2P)`, `B=∫_[m,T] D_H3`, and `J` is the captured finite cutoff.
The other branches (terminal Fourier carrier, attained early source, kinetic clock,
remaining-time compression, and pure viscous tail) are retained on the SAME
minimal first-crossing windows, as are the disjoint viscous charges and outer
frequency/gauge escape. Since pointwise dissipation at selected times need not
be controlled by its integrable total, no continuation is claimed.

Proof declarations:
- `thirdFull_scalar_quinticProduct_twoSliceMonotonicity244`
- `thirdFullPhysical_lateQuinticProduct_twoActualViscousSlices244`
- `thirdFullPhysical_noH3Trace_prescribedGauge_lateTwoViscousSlices244`

Run the audit registrar, `proof/generate_index.py`, individual Lean compilation,
module build, root build and baseline audit on the pinned toolchain. No `sorry`,
`admit`, or new axiom is intended.
