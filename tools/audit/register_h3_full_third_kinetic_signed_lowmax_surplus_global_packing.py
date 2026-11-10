#!/usr/bin/env python3
"""Register integrated signed-surplus selection and global certified H3 packing."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxSurplusGlobalPacking'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('ThirdFullKineticSignedLowMaxSurplusPackingActive244',)
THEOREMS = (
    'thirdFullPhysical_signedLowMax_surplusPackingActive_adverseTime244',
    'thirdFullPhysical_kineticGaps_signedLowMax_surplusGlobalPacking244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS) for line in
               ('#check ' + NS + name, '#print axioms ' + NS + name))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    lines = set(old.splitlines())
    missing = [line for line in wanted if line not in lines]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f'missing file: {path}')
    code = source.read_text(encoding='utf-8')
    for name in DEFS:
        pat = r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b'
        if len(re.findall(pat, code)) != 1:
            parser.error(f'missing or duplicate definition: {name}')
    for name in THEOREMS:
        pat = r'(?m)^theorem\s+' + re.escape(name) + r'\b'
        if len(re.findall(pat, code)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    cleaned = re.sub(r'/-.*?-/', '', code, flags=re.S)
    cleaned = re.sub(r'--[^\n]*', '', cleaned)
    if re.search(r'\b(?:sorry|admit|axiom)\b', cleaned):
        parser.error('unproven placeholder or axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate registration: {path}: {line}')
    print(f'PASS: signed LowMax integrated surplus global packing; '
          f'{len(DEFS)} definition, {len(THEOREMS)} theorems')


if __name__ == '__main__':
    main()
