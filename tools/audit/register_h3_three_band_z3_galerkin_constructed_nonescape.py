#!/usr/bin/env python3
"""Register actual constructed finite-Galerkin non-escape and speed results."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandZ3GalerkinConstructedNonEscape')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinWiener_singleMode_le244',
    'thirdFullThreeBand_z3GalerkinWeight_one_le244',
    'thirdFullThreeBand_z3GalerkinFiniteState_norm_le_of_Wiener244',
    'thirdFullThreeBand_z3GalerkinFiniteField_norm51000_100Ball244',
    'thirdFullThreeBand_z3GalerkinFiniteField_intervalIntegrable244',
    'thirdFullThreeBand_z3GalerkinConstructedLocal_nonEscapeAndSpeed244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))


def insert_missing(path: Path, rows, prepend=False):
    content = path.read_text(encoding='utf-8')
    present = set(content.splitlines())
    missing = [row for row in rows if row not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + content if prepend else content.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    opts = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error('missing ' + str(path))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', scrubbed):
        parser.error('unproved assertion found')
    if any(x != x.rstrip() for x in code.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing or duplicate theorem ' + name)
    if opts.apply:
        insert_missing(root, (IMPORT,))
        insert_missing(audit, (IMPORT,), prepend=True)
        insert_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error(f'missing or duplicate registration: {path}: {row}')
    print(f'PASS: constructed non-escape registry; {len(THEOREMS)} theorems and '
          f'{len(CHECKS)} axiom/declaration probes')


if __name__ == '__main__':
    main()
