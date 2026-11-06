#!/usr/bin/env python3
"""Register same-window physical source-to-moving-raw-Fourier transport."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
MODULE = 'FullThirdSolenoidalTerminalProfileCriticalEighthWindowRawTransport'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_rawHighpass_transport_le_sourceL1244',
    'thirdFullPhysical_rawHighpass_window_le_sourceL1244',
    'thirdFullPhysical_rawBandMass_window_le_sourceL1244',
    'thirdFullPhysical_minimalWindows_uniformMovingRawMass244',
    'thirdFullPhysical_noH3Trace_criticalEighth_uniformWindowRawMass244',
)
IMPORT = 'import ' + PREFIX + MODULE
CHECKS = tuple(s for name in THEOREMS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    extra = [line for line in lines if line not in present]
    if extra:
        addition = '\n'.join(extra) + '\n'
        path.write_text(
            addition + old if prepend else old.rstrip('\n') + '\n' + addition,
            encoding='utf-8',
        )


def main():
    parser = argparse.ArgumentParser()
    m = parser.add_mutually_exclusive_group(required=True)
    m.add_argument('--apply', action='store_true')
    m.add_argument('--check', action='store_true')
    args = parser.parse_args()

    module_file = ROOT / (PREFIX.replace('.', '/') + MODULE + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (module_file, root_file, audit_file):
        if not p.is_file():
            parser.error(f'missing: {p}')
    src = module_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
            parser.error(f'missing/repeated theorem {name}')
    stripped = re.sub(r'/-.*?-/', '', src, flags=re.S)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
        parser.error('proof placeholder or unsafe axiom in source')
    if any(line.rstrip() != line for line in src.splitlines()):
        parser.error('trailing whitespace in source')
    if args.apply:
        ensure_once(root_file, [IMPORT])
        ensure_once(audit_file, [IMPORT], prepend=True)
        ensure_once(audit_file, CHECKS)
    for p, lines in ((root_file, [IMPORT]), (audit_file, [IMPORT, *CHECKS])):
        rows = p.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if rows.count(line) != 1:
                parser.error(f'expected exactly once: {line!r} in {p}')
    print(f'PASS: {MODULE}; {len(THEOREMS)} theorems; '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
