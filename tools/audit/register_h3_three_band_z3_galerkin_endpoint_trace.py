#!/usr/bin/env python3
"""Register full Leray finite-Galerkin temporal Lipschitz and endpoint sequence results."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinEndpointTrace'
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinFiniteODE_preterminalLipschitz51000_244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_exists244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_endpointSequence_nonescape244',
    'thirdFullThreeBand_z3GalerkinConstructedLocal_temporalLipschitz244',

)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path: Path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    known = set(original.splitlines())
    missing = [row for row in rows if row not in known]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + original if prepend else original.rstrip('\n') + '\n' + block,
                        encoding='utf-8')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, root, audit):
        if not p.is_file(): parser.error('missing: ' + str(p))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', scrubbed):
        parser.error('unproved source assertion')
    if any(ln != ln.rstrip() for ln in code.splitlines()):
        parser.error('trailing whitespace')
    for n in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(n) + r'\b', code)) != 1:
            parser.error('missing/duplicate theorem: ' + n)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for path, expected in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row) != 1:
                parser.error('missing/duplicate registration: ' + str(path) + ': ' + row)
    print(f'PASS: endpoint-trace registry, {len(THEOREMS)} results, {len(CHECKS)} probes')

if __name__ == '__main__':
    main()
