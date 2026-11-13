#!/usr/bin/env python3
"""Register exact selected annular outer kinetic carrier constraints."""
import argparse
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularOuterCarrierDominance')
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_sharpHighpass_annulusOuter_normSquare244',
    'thirdFullPhysical_actualSharpHighMass_annulusOuter_exact244',
    'thirdFullKinetic_outerCarrier_from_annularBudget244',
    'thirdFullPhysical_wideAnnularPositiveDeficit_outerCarrier244',
    'thirdFullPhysical_doubleAperture_outerCarrier119of128244',
    'thirdFullPhysical_finiteDissipation_selectedNaturalOuterCarrier244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(stmt for name in THEOREMS for stmt in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def register(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in lines if line not in present]
    if missing:
        addition = '\n'.join(missing) + '\n'
        path.write_text(addition + old if prepend else old.rstrip('\n') + '\n' + addition,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()

    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    mainlean = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, mainlean, audit):
        if not path.is_file():
            parser.error(f'missing: {path}')
    body = source.read_text(encoding='utf-8')
    sanitized = re.sub(r'/-.*?-/', '', body, flags=re.S)
    sanitized = re.sub(r'--[^\n]*', '', sanitized)
    if re.search(r'\b(?:sorry|admit|axiom)\b', sanitized):
        parser.error('Lean proof placeholder')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', sanitized))
        if count != 1:
            parser.error(f'expected exactly one theorem {name}: found {count}')
    if args.apply:
        register(mainlean, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, lines in ((mainlean, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        content = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if content.count(line) != 1:
                parser.error(f'expected one {line} in {path}')
    print(f'PASS: exact annular outer carrier ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
