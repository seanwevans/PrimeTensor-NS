#!/usr/bin/env python3
"""Idempotent root and audit registration for fixed-component L¹ residual escape."""

from pathlib import Path
import argparse
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalFixedComponentResidualEscape'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_FILE = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
IMPORT = 'import ' + MODULE
NAMES = (
    'h3Critical_scalarL2_terminal_nonintegrability_survives_L1_correction',
    'h3Critical_scalarL2_terminal_residual_cofinal_spikes',
    'h3Critical_noL2Trace_fixed_coordinate_survives_L1_correction_family',
    'h3Critical_noL2Trace_fixed_coordinate_highpass_escape_of_lowpass_L1',
)
CHECKS = tuple(row for name in NAMES for row in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_unique(path: Path, wanted: tuple[str, ...], *, at_head=False):
    current = path.read_text()
    old_lines = current.splitlines()
    missing = [line for line in wanted if line not in old_lines]
    if not missing:
        return
    payload = '\n'.join(missing) + '\n'
    if at_head:
        path.write_text(payload + current)
    else:
        path.write_text(current.rstrip('\n') + '\n' + payload)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    choices = p.add_mutually_exclusive_group(required=True)
    choices.add_argument('--apply', action='store_true')
    choices.add_argument('--check', action='store_true')
    args = p.parse_args()

    for path in (SOURCE, ROOT_FILE, AUDIT_FILE):
        if not path.is_file():
            p.error('Missing input: ' + str(path.relative_to(ROOT)))

    source = SOURCE.read_text()
    for name in NAMES:
        if source.count('theorem ' + name + '\n') != 1:
            p.error('Missing or duplicate theorem: ' + name)
    # Deliberately no regex that could match natural-language documentation.
    for pattern in ('\nsorry\n', '\nadmit\n', '\naxiom '):
        if pattern in source:
            p.error('Forbidden proof placeholder: ' + repr(pattern))

    if args.apply:
        append_unique(ROOT_FILE, (IMPORT,))
        append_unique(AUDIT_FILE, (IMPORT,), at_head=True)
        append_unique(AUDIT_FILE, CHECKS)

    for path, wanted in ((ROOT_FILE, (IMPORT,)),
                         (AUDIT_FILE, (IMPORT,) + CHECKS)):
        rows = path.read_text().splitlines()
        for line in wanted:
            if rows.count(line) != 1:
                p.error('Registration missing or duplicate in ' + str(path.relative_to(ROOT)) + ': ' + line)

    print('PASS: 1 proof import, 4 theorems, 4 #check, 4 #print axioms')


if __name__ == '__main__':
    main()
