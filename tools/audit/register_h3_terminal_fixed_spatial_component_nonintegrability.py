#!/usr/bin/env python3
"""Register the fixed physical coordinate terminal L1 obstruction.

--apply appends root imports and 8 theorem/axiom audits exactly once.
--check verifies those declarations and imports without changing files.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MOD = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedSpatialComponentNonintegrability'
FILE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_IMPORT = 'import ' + MOD
NAMES = (
    'h3Critical_scalarL2_source_integrable_mono_terminal_tail',
    'h3Critical_fin3_hilbert_intervalIntegrable_iff_components',
    'h3Critical_fin3_fixed_component_nonintegrable_of_vector_nonintegrable',
    'h3Critical_continuous_scalarL2_integrable_of_terminal_ceiling',
    'h3Critical_continuous_scalarL2_nonintegrable_forces_spikes',
    'h3Critical_fin3_fixed_component_nonintegrability_and_spikes',
    'h3Critical_noL2Trace_fixed_projected_coordinate_nonintegrable_and_spikes',
    'h3Critical_noL2Trace_fixed_laplacian_or_leray_coordinate_nonintegrable_and_spikes',
)
AUDIT = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, required: tuple[str, ...], at_head: bool = False) -> None:
    original = path.read_text()
    existing = set(original.splitlines())
    new = [line for line in required if line not in existing]
    if new:
        block = '\n'.join(new) + '\n'
        path.write_text(block + original if at_head else original.rstrip('\n') + '\n' + block)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply', action='store_true')
    g.add_argument('--check', action='store_true')
    args = ap.parse_args()
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root_file, audit_file, FILE):
        if not path.is_file():
            ap.error('missing: ' + str(path.relative_to(ROOT)))
    if args.apply:
        append_missing(root_file, (ROOT_IMPORT,))
        append_missing(audit_file, (ROOT_IMPORT,), at_head=True)
        append_missing(audit_file, AUDIT)
    for path, required in ((root_file, (ROOT_IMPORT,)),
                           (audit_file, (ROOT_IMPORT,) + AUDIT)):
        lines = path.read_text().splitlines()
        for line in required:
            if lines.count(line) != 1:
                ap.error(f'expected exactly one {line!r} in {path.relative_to(ROOT)}')
    lean = FILE.read_text()
    for name in NAMES:
        if lean.count('theorem ' + name + '\n') != 1:
            ap.error(f'missing or duplicate theorem declaration: {name}')
    for token in ('sorry', 'admit', 'unsafe axiom'):
        import re
        if re.search(r'\b' + re.escape(token) + r'\b', lean):
            ap.error(f'forbidden placeholder {token!r}')
    print('PASS: one root import, one audit import, 8 theorems, 8 #check and 8 #print axioms')
    return 0


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    raise SystemExit(main())
