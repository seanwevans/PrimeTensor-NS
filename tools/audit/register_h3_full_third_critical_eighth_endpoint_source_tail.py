#!/usr/bin/env python3
"""Register terminal physical-source primitive and endpoint-tail eighth moment."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
MODULE = 'FullThirdSolenoidalTerminalProfileCriticalEighthEndpointSourceTail'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_terminalProjectedSource_primitive_exact244',
    'thirdFullPhysical_terminalHighpass_le_endpointPlusSourceTail244',
    'thirdFullPhysical_criticalEighth_window_endpointTailMomentBarrier244',
    'thirdFullPhysical_noH3Trace_criticalEighth_endpointTailMomentBarrier244',
)
IMPORT = 'import ' + PREFIX + MODULE
CHECKS = tuple(s for name in THEOREMS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        block = '\n'.join(new) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()

    source_file = ROOT / (PREFIX.replace('.', '/') + MODULE + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source_file, root_file, audit_file):
        if not path.is_file():
            parser.error(f'missing {path}')

    source = source_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        matches = re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)
        if len(matches) != 1:
            parser.error(f'missing/repeated theorem {name}: {source_file}')
    stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
        parser.error(f'proof placeholder in {source_file}')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error(f'trailing whitespace in {source_file}')

    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, lines in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        data = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if data.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: {MODULE}, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
