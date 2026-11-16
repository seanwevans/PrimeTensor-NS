#!/usr/bin/env python3
"""Register finite-mode exact three-band Navier-Stokes Leray transfer probe."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalKineticThreeBandLerayTransferProbe'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_dotAdd_right244',
    'thirdFullThreeBand_workConserves244',
    'thirdFullThreeBand_exampleSolenoidal244',
    'thirdFullThreeBand_exampleRadialOrdering244',
    'thirdFullThreeBand_exampleSignedWork244',
    'thirdFullThreeBand_exampleProjectedWork244',
    'thirdFullThreeBand_bothOutwardFluxesPositive244',
)
DEFS = (
    'thirdFullThreeBandDot244',
    'thirdFullThreeBandLeray244',
    'thirdFullThreeBandProjectedLow244',
    'thirdFullThreeBandProjectedMid244',
    'thirdFullThreeBandProjectedHigh244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(
    line for name in (*DEFS, *THEOREMS)
    for line in ('#check ' + NS + name,
                 '#print axioms ' + NS + name)
)


def register(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in entries if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--apply', action='store_true')
    action.add_argument('--check', action='store_true')
    args = parser.parse_args()

    source_path = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_path = ROOT / 'PrimeTensor.lean'
    audit_path = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source_path, root_path, audit_path):
        if not path.is_file():
            parser.error(f'missing expected file: {path}')

    source = source_path.read_text(encoding='utf-8')
    no_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    no_comments = re.sub(r'--[^\n]*', '', no_comments)
    if re.search(r'\b(?:sorry|admit|axiom)\b', no_comments):
        parser.error('source contains a proof placeholder or new axiom')
    if any(line != line.rstrip() for line in source.splitlines()):
        parser.error('trailing whitespace in Lean source')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or duplicated theorem {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or duplicated definition {name}')

    if args.apply:
        register(root_path, (IMPORT,))
        register(audit_path, (IMPORT,), prepend=True)
        register(audit_path, CHECKS)
    for path, wanted in ((root_path, (IMPORT,)),
                         (audit_path, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate registration: {path}: {line}')
    print(f'PASS: three-band Leray probe ({len(THEOREMS)} theorems, '
          f'{len(DEFS)} definitions, {len(CHECKS)} trust probes)')


if __name__ == '__main__':
    main()
