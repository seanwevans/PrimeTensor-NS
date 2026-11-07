#!/usr/bin/env python3
"""Register same-witness natural kinetic annular charges and cutoff escape."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSecondaryAnnularCutoffEscape'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_secondaryHighRadialSpike_kineticAnnularCharge244',
    'thirdFullPhysical_secondaryTwoSlice_forcesKineticAnnularCharge244',
    'thirdFull_scalar_kineticAnnularRate_forces_outerCutoffEscape244',
    'thirdFullPhysical_secondaryKineticAnnularCharge_outerCutoffEscape244',
    'thirdFullPhysical_secondaryHighRadialLedger_to_naturalKineticAnnular244',
    'thirdFullPhysical_noH3Trace_prescribedGauge_secondaryNaturalKineticAnnular244',
)
DEFS = (
    'ThirdFullSecondaryNaturalKineticAnnularCharge244',
    'ThirdFullLateRetainedPrimarySecondaryNaturalKineticAnnularCofinalLedger244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS + DEFS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    lean = ROOT / (MODULE.replace('.', '/') + '.lean')
    main_lean = ROOT / 'PrimeTensor.lean'
    audit_lean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (lean, main_lean, audit_lean):
        if not p.is_file():
            parser.error('missing file ' + str(p))
    source = lean.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or repeated theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing or repeated definition: ' + name)
    sans_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', sans_comments):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in source.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        ensure_once(main_lean, (IMPORT,))
        ensure_once(audit_lean, (IMPORT,), prepend=True)
        ensure_once(audit_lean, CHECKS)
    for p, required in ((main_lean, (IMPORT,)), (audit_lean, (IMPORT,) + CHECKS)):
        lines = p.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error('missing or repeated audit: ' + line)
    print('PASS: same-witness kinetic annular cutoff escape; '
          f'{len(THEOREMS)} theorems, {len(DEFS)} definitions, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
