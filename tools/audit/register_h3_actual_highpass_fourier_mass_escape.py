#!/usr/bin/env python3
"""Register actual Fourier high-pass source identification and terminal mass escape."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualHighpassFourierMassEscape'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT_FILE = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_radialFrequencyBelow_neg_iff',
    'h3Critical_fourierSharpLowCutoff_preserves_hermitian',
    'h3Critical_scalarFourier_physicalSharpLowCutoff_eq',
    'h3Critical_scalarFourier_physicalHighpass_eq',
    'h3Critical_fourierSharpHighpass_ae',
    'h3Critical_fourierSharpHighpass_norm_sq_eq_integral',
    'h3Critical_actualProjectedHighpassFourier_eq_physical',
    'h3Critical_actualProjectedFourierSource_eq_rawRHS',
    'h3Critical_actualProjectedHighpassFourier_norm_eq_physical',
    'h3Critical_intervalIntegrable_of_scalarFourier_intervalIntegrable',
    'h3Critical_noL2Trace_actualHighpassFourier_escape',
    'h3Critical_noL2Trace_actualHighpassFourierMass_escape',
)
DEFS = (
    'h3CriticalActualProjectedFourierSource',
    'h3CriticalActualProjectedHighpassFourierSource',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for name in THEOREMS + DEFS for stmt in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))


def append_missing(path: Path, lines, prepend=False):
    original = path.read_text(encoding='utf-8')
    present = set(original.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text(chunk + original if prepend else original.rstrip('\n') + '\n' + chunk,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT_FILE):
        if not path.is_file():
            parser.error('missing ' + str(path))
    if args.apply:
        append_missing(ROOT_LEAN, (IMPORT,))
        append_missing(AUDIT_FILE, (IMPORT,), prepend=True)
        append_missing(AUDIT_FILE, CHECKS)
    for path, required in ((ROOT_LEAN, (IMPORT,)), (AUDIT_FILE, (IMPORT,) + CHECKS)):
        content = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if content.count(line) != 1:
                parser.error('expected one occurrence of ' + repr(line) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    for name in DEFS:
        if source.count('noncomputable def ' + name + '\n') != 1:
            parser.error('missing or duplicate def: ' + name)
    for bad in ('sorry', 'admit', 'unsafe axiom'):
        if bad in source:
            parser.error('placeholder forbidden: ' + bad)
    print('PASS:', len(THEOREMS), 'theorems,', len(DEFS), 'definitions,',
          len(CHECKS), 'audit checks/axiom prints')


if __name__ == '__main__':
    main()
