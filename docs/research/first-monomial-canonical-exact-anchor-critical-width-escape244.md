# Critical-width cap forces actual anchor H³ energy and spectral escape

Base commit: `1be7aeb3`.

On the reconstructed canonical exact-anchor, pairwise-disjoint quadratic-sharp windows, the previous module proves, conditionally on a ninth/eighth minimal annulus-width cap,

`(v(k)+1)^3 < 65536 (V+1) E₃(τ(v(k)))^4` eventually.

The selected natural indices `v(k)` are strictly increasing, so their cubic radial scale tends to infinity. Because physical `E₃≥1`, this forces **actual normalized physical H³ energy at the original window anchors** to infinity. The exact identity `E₃(t)=1+Σⱼ‖U₃(t)ⱼ‖²≤1+3‖U₃(t)‖²` then forces the exact spectral coefficient `K(v(k))=‖U₃(τ(v(k)))‖` to infinity.

The previously established physical fixed-frequency coercivity theorem can then be applied at the same anchor sequence, after any interior kinetic anchor `b`, proving `D₃(τ(v(k)))/K(v(k))²→+∞`.

**Scope:** The ninth/eighth cap remains an *eventual hypothesis*, and the no-terminal-H³-trace premise and integrability are retained. The dissipation conclusion is pointwise in physical time; an integrable function can have diverging peaks along shrinking disjoint time windows. No time-uniform persistence scale or unconditional continuation is claimed. The new witness selection still preserves its canonical minimal annuli and attained source envelopes.

**Validation:** Static source inspections, audit registrar syntax/idempotence, and ZIP CRC; local `lake build` is required to verify elaboration.
