# Restore SixIntegral to audited root coverage

The local baseline after the full H3 energy barrier compilation found an orphaned
`PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadSixIntegral`
source file. It is not in the known five standalone targets and is absent from
`PrimeTensor.lean`. The root build thus does not validate the source.

This checkpoint **does not alter SixIntegral's proof**. The run script first checks
it with `lake env lean .../FirstMonomialTriadSixIntegral.lean`, and only if that
succeeds registers it as a root import. Then run source-index regeneration and
checks, Lean root/contract builds and the full baseline. This preserves the
existing five deliberate standalone targets and the matching
`known-source-gaps.json`; neither is loosened to hide the orphan.

If the initial SixIntegral check fails, stop and repair its actual Lean error.
The previous local root build's success does not establish that SixIntegral
compiles. The audit should not be bypassed or its expected exceptions widened.
