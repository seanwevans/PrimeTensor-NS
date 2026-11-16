#!/usr/bin/env python3
"""Register three-band analytic-Wiener quantitative persistence bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalKineticThreeBandAnalyticWienerPersistence')
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = (
    'thirdFullThreeBandWienerMajorant244',
    'thirdFullThreeBandWienerTimeCap244',
    'thirdFullThreeBandWienerViscosityCap244',
    'thirdFullThreeBandInitialLowerPairFlux244',
    'thirdFullThreeBandInitialUpperPairFlux244',
    'thirdFullThreeBandWienerDifferenceCap244',
    'thirdFullThreeBandWienerFluxErrorCap244',
)
THEOREMS = (
    'thirdFullThreeBand_initialPairFluxes244',
    'thirdFullThreeBand_wienerRadiusLinearMargin244',
    'thirdFullThreeBand_wienerDifferenceCap_le244',
    'thirdFullThreeBand_wienerFluxErrorCap_lt_tenth244',
    'thirdFullThreeBand_wienerTimeCap_positive244',
    'thirdFullThreeBand_outwardFluxPersistence_of_wienerBounds244',
    'thirdFullThreeBand_wienerPhysicalTime_to_dimensionless244',
    'thirdFullThreeBand_wienerViscosityScaling244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS)
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
    for kind, names in ((r'def', DEFS), (r'theorem', THEOREMS)):
        for name in names:
            pat = r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pat, code)) != 1:
                ap.error(f'missing or duplicate {kind}: {name}')
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                ap.error(f'missing/duplicate registration: {path}: {line}')
    print(f'PASS: analytic Wiener three-band bridge ({len(DEFS)} definitions, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} declaration/axiom checks)')


if __name__ == '__main__':
    main()
