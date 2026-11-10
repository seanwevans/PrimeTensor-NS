#!/usr/bin/env python3
"""Register and audit the sharp cubic-rate 5/3 scalar counterprofile."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalFiveThirdsScalarSharpness'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = ('thirdFullKinetic_cubicRateSaturatingProfile_nonneg244', 'thirdFullKinetic_cubicRateSaturatingProfile_exactCubic244', 'thirdFullKinetic_cubicRateSaturatingProfile_weight244', 'thirdFullKinetic_cubicRateSaturatingProfile_criticalNonintegrable244', 'thirdFullKinetic_cubicRateSaturatingProfile_supercriticalIntegrable244', 'thirdFullKinetic_cubicRate_supercriticalWeight_hasCounterprofile244')
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in THEOREMS for item in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    p = argparse.ArgumentParser()
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = p.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    imports = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, imports, audit):
        if not path.is_file():
            p.error(f'missing file: {path}')
    code = source.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            p.error(f'missing/duplicate theorem: {name}')
    cleaned = re.sub(r'/-.*?-/', '', code, flags=re.S)
    cleaned = re.sub(r'--[^\n]*', '', cleaned)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', cleaned):
        p.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        p.error('source contains trailing whitespace')
    if args.apply:
        add_missing(imports, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((imports, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                p.error(f'missing/duplicate registration: {path}: {line}')
    print(f'PASS: 5/3 cubic-rate scalar sharpness; {len(THEOREMS)} declarations')


if __name__ == '__main__':
    main()
