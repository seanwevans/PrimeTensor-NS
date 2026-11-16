#!/usr/bin/env python3
"""Register uniform discrete Wiener envelope and finite kinetic ceiling."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandWienerKineticCharge')
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_allDegreeWienerEnvelopes244',
    'thirdFullThreeBand_degreeAbsorbedByWiener244',
    'thirdFullThreeBand_finiteSquares_le_squareSum244',
    'thirdFullThreeBand_finiteOrderedKernelBound244',
    'thirdFullThreeBand_finiteWienerKineticCeiling244',
    'thirdFullThreeBand_viscousChargeFromGradientCap244',
    'thirdFullThreeBand_persistentTransfer_noUniformViscousCharge244',
    'thirdFullThreeBand_smallPositiveViscosityForCharge244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def add_missing(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else
                        old.rstrip('\n') + '\n' + block, encoding='utf-8')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = ap.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (src, root, audit):
        if not path.is_file():
            ap.error(f'missing required file: {path}')
    code = src.read_text(encoding='utf-8')
    stripped = re.sub(r'/-.*?-/', '', code, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    if re.search(r'\b(?:sorry|admit|axiom)\b', stripped):
        ap.error('proof placeholder or additional axiom')
    if any(x != x.rstrip() for x in code.splitlines()):
        ap.error('trailing whitespace')
    for name in THEOREMS:
        pat = r'(?m)^theorem\s+' + re.escape(name) + r'\b'
        if len(re.findall(pat, code)) != 1:
            ap.error(f'missing or duplicate theorem: {name}')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                ap.error(f'missing/duplicate registration: {path}: {line}')
    print(f'PASS: all-degree/finite-frequency Wiener kinetic charge '
          f'({len(THEOREMS)} theorems, {len(CHECKS)} declaration/axiom checks)')


if __name__ == '__main__':
    main()
