#!/usr/bin/env python3
"""Register fixed-inner selected annulus terminal bandlimit theorems."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularFixedInnerTerminalBandlimit'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_outerRetention_tight_forces_innerVanishing244',
    'thirdFullKinetic_naturalOuter_eventually_double244',
    'thirdFullPhysical_fixedSnapshot_naturalOuterHighMass_tendsto_zero244',
    'thirdFullPhysical_fixedSnapshot_noPersistentWidePositiveDeficit244',
    'thirdFullPhysical_finiteDissipation_cofinalFixedInnerHighMassVanishes244',
    'thirdFullPhysical_finiteDissipation_cofinalFixedInner_terminalBandlimit244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name))


def register(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        extra = '\n'.join(missing) + '\n'
        path.write_text(extra + old if prepend else old.rstrip('\n') + '\n' + extra,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    rootlean = ROOT / 'PrimeTensor.lean'
    auditlean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, rootlean, auditlean):
        if not path.is_file():
            parser.error(f'missing {path}')
    content = source.read_text(encoding='utf-8')
    cleaned = re.sub(r'/-.*?-/', '', content, flags=re.S)
    cleaned = re.sub(r'--[^\n]*', '', cleaned)
    if re.search(r'\b(?:sorry|admit|axiom)\b', cleaned):
        parser.error('proof placeholder or added axiom found')
    for name in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', cleaned))
        if count != 1:
            parser.error(f'theorem missing/duplicated: {name} ({count})')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for path, expected in ((rootlean, (IMPORT,)),
                           (auditlean, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error(f'expected one occurrence of {line} in {path}')
    print(f'PASS: fixed-inner physical terminal bandlimit ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
