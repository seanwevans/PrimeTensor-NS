#!/usr/bin/env python3
"""Idempotent registration and declaration/axiom audit for full high-max tail."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
ITEMS = (
    ('FullThirdSolenoidalOuterHighMaxTail', (
        'thirdFullHighMaxSet244',
        'thirdFullMinFirstHighMaxSector244',
        'thirdFullMinLastHighMaxSector244',
    ), (
        'thirdFullHighMaxSet_measurable244',
        'thirdFullMinFirstHighMaxSector_measurable244',
        'thirdFullMinLastHighMaxSector_measurable244',
        'thirdFull_lowFirst_highMax_forces_middleLastHigh244',
        'thirdFull_lowLast_highMax_forces_firstMiddleHigh244',
        'thirdFullSchwartzSixthPowerFlux_firstHighMaxIntegral_le_H3Tail244',
        'thirdFullSchwartzSixthPowerFlux_lastHighMaxIntegral_le_H3Tail244',
        'thirdFullWeightedSchwartz_firstHighMaxIntegral_le244',
        'thirdFullWeightedSchwartz_lastHighMaxIntegral_le244',
    )),
    ('FullThirdSolenoidalGlobalHighMaxTail', (), (
        'thirdFullMinMiddleHighMaxSector_eq_inter244',
        'thirdFullHighMaxSectors_cover244',
        'thirdFullHighMaxFirstMiddle_disjoint244',
        'thirdFullHighMaxFirstMiddleLast_disjoint244',
        'thirdFullSchwartzSixthPowerFlux_highMaxIntegralSplit244',
        'thirdFullSchwartzSixthPowerFlux_highMaxIntegral_le_H3Tail244',
        'thirdFullWeightedSchwartz_highMaxIntegral_le244',
        'exists_thirdFullPhysicalSnapshot_highMaxTailVanishing244',
    )),
)
IMPORTS = tuple('import ' + PREFIX + module for module, _, _ in ITEMS)
NAMES = tuple(name for _, defs, thms in ITEMS for name in (*defs, *thms))
CHECKS = tuple(line for name in NAMES for line in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
))


def ensure_lines(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        addition = '\n'.join(new) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root_file = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root_file, audit):
        if not path.is_file():
            parser.error(f'missing {path}')
    for module, defs, thms in ITEMS:
        source = ROOT / (PREFIX.replace('.', '/') + module + '.lean')
        if not source.is_file():
            parser.error(f'missing {source}')
        src = source.read_text(encoding='utf-8')
        for name in defs:
            if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', src)) != 1:
                parser.error(f'missing or repeated definition {name} in {source}')
        for name in thms:
            if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
                parser.error(f'missing or repeated theorem {name} in {source}')
        # Exclude comments before checking for proof placeholders.
        without_comments = re.sub(r'/-.*?-/', '', src, flags=re.S)
        if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
            parser.error(f'proof placeholder in {source}')
    if args.apply:
        ensure_lines(root_file, IMPORTS)
        ensure_lines(audit, IMPORTS, prepend=True)
        ensure_lines(audit, CHECKS)
    for path, lines in ((root_file, IMPORTS), (audit, IMPORTS + CHECKS)):
        body = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if body.count(line) != 1:
                parser.error(f'expected one {line!r} in {path}')
    print(f'PASS: {len(ITEMS)} source modules, {len(NAMES)} declarations, '
          f'{len(CHECKS)} declaration/axiom audit lines')


if __name__ == '__main__':
    main()
