#!/usr/bin/env bash
# Rebuild the changed dependency before checking the new canonical module.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

BASE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzMatchedEnergyCauchy244
REFERENCE=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedReferenceIndependence244
CANONICAL=PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzWeightedCanonicalCompletion244
FILE=PrimeTensor/Fluid/Vorticity/Continuation/H3/Control/FirstMonomialTriadLowQuarterPoint3SchwartzWeightedCanonicalCompletion244.lean

python3 tools/audit/register_first_monomial_schwartz_weighted_canonical_completion244.py

# `lake env lean File.lean` checks a file but does not produce an importable
# .olean by default. `lake build` must update imported modules first.
lake build "$BASE"
lake build "$REFERENCE"
lake env lean "$FILE"
lake build "$CANONICAL"
