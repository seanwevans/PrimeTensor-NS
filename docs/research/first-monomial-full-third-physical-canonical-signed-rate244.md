# Exact canonical signed H³ PDE rate at the physical snapshot

Checkpoint: `9a2796a1` — **identify physical H3 972-term gradient with canonical Schwartz transport**.

## Previous result

For an actual preterminal Fourier-compatible H³ Navier–Stokes slice,

\[
T_3^{\mathrm{physical}}(u,t)
  = \mathcal{C}_3(U(t))
  = \mathcal{G}_3(U(t)) + 3\mathcal{M}_3(U(t)),
\]

where `\mathcal{G}_3` is the choice-independent 972-term 3–3–1 gradient completion and `\mathcal{M}_3` the choice-independent signed 243-slot 3–2–2 interpolation completion. This is equality of the **actual** old physical commutator with the weighted spectral Schwartz completion, not a regularity estimate.

## New PDE-facing identity

Define the canonical spectral path from the actual time-slice integrability, measurability and Fourier compatibility already supplied by `LoggedPreterminalH3PathAdmissible`. The associated positive scalar is

\[
\mathcal R_{\rm can}(t) = \max\left\{0,\;
 24 C_1\sqrt{E(t)}-
 \frac{\mathcal C_3(U(t))+2D(t)}{E(t)}-4422\right\}.
\]

The proof shows, pointwise on every energy-class tail,

\[
E'(t)+2D(t) \le 24 C_1\sqrt{E(t)} E(t) - \mathcal C_3(U(t)),
\quad \frac{E'(t)}{E(t)} \le
24 C_1\sqrt{E(t)}-\frac{\mathcal C_3(U(t))+2D(t)}{E(t)}.
\]

The canonical remainder `\mathcal R_{\rm can}` agrees pointwise with the existing signed physical top-transport remainder, so the old continuation theorem immediately yields:

- `\mathcal R_{\rm can}` integrable over an energy-class tail **implies smooth continuation**;
- hypothetical failure of continuation makes `\mathcal R_{\rm can}` nonintegrable on **every strict terminal subtail**;
- under hypothetical failure of continuation, every strict subtail and every `M ≥ 0` contains a time at which

\[
(4422+M)E(t)+2D(t)
  < 24 C_1\sqrt{E(t)}E(t)-\mathcal C_3(U(t)).
\]

There is also a direct sufficient condition: if

\[
24 C_1\sqrt{E(t)}E(t)
  \le 4422 E(t)+\mathcal C_3(U(t))+2D(t)
\]

throughout a strict tail, then the canonical remainder vanishes on that tail and the old H³ continuation theorem applies.

## Boundary and interpretation

These statements do **not** prove any universal favorable bound on `\mathcal C_3`, or unconditional regularity. They identify precisely the necessary adverse spectral cubic phenomenon under hypothetical nonextension. The bound above is a **new criterion**, not a proved inequality for all flows. All statements retain the original admissibility and energy-class requirements. No extra Schwartz realization, third-jet L⁴ hypothesis or unproved nonlinear trace is inserted.

Source module: `PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3FullThirdPhysicalCanonicalSignedRate244.lean`.
