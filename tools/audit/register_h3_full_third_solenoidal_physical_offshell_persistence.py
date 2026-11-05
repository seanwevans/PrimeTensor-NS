#!/usr/bin/env python3
"""Register physical H3 off-shell persistence under moving annuli."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MOD = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalPhysicalOffshellPersistence'
SOURCE = ROOT / (MOD.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_shellZero244',
    'thirdFullSchwartzSixthPowerFlux_offshell_tendsto_of_moments244',
    'exists_thirdFullPhysicalSnapshot_offshellTransportPersistence244',
)
IMPORT = 'import ' + MOD
CHECKS = [x for name in THEOREMS for x in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
)]


def ensure_lines(path, needed, prepend=False):
    old = path.read_text(encoding='utf-8')
    current = set(old.splitlines())
    new = [line for line in needed if line not in current]
    if not new:
        return
    extra = '\n'.join(new) + '\n'
    path.write_text((extra + old) if prepend else (old.rstrip('\n') + '\n' + extra), encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error(f'missing {path}')
    if args.apply:
        ensure_lines(ROOT_LEAN, [IMPORT])
        ensure_lines(AUDIT, [IMPORT], prepend=True)
        ensure_lines(AUDIT, CHECKS)
    for path, lines in ((ROOT_LEAN, [IMPORT]), (AUDIT, [IMPORT] + CHECKS)):
        body = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if body.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    body = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', body)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', body):
        parser.error('proof placeholder forbidden')
    print(f'PASS: {len(THEOREMS)} theorems / {len(CHECKS)} axiom-audit entries')


if __name__ == '__main__':
    main()
