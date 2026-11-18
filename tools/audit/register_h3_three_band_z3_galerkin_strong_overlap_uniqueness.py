#!/usr/bin/env python3
"""Register real finite-Leray compact-ball Lipschitz and overlap uniqueness."""
import argparse, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinStrongOverlapUniqueness'
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinFiniteField_lipschitzOnClosedBall244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_uniqueOnCompactBall244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_automaticOverlapUnique244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def append_unique(path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    known = set(original.splitlines())
    missing = [line for line in rows if line not in known]
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
    mainfile = ROOT / 'PrimeTensor.lean'
    auditfile = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, mainfile, auditfile):
        if not p.is_file(): parser.error('missing: ' + str(p))
    code = source.read_text(encoding='utf-8')
    scrubbed = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrubbed = re.sub(r'--[^\n]*', '', scrubbed)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrubbed):
        parser.error('unproved or unsafe source')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error('missing or duplicate theorem: ' + name)
    if args.apply:
        append_unique(mainfile, (IMPORT,))
        append_unique(auditfile, (IMPORT,), prepend=True)
        append_unique(auditfile, CHECKS)
    for p, rows in ((mainfile,(IMPORT,)),(auditfile,(IMPORT,*CHECKS))):
        lines=p.read_text(encoding='utf-8').splitlines()
        for line in rows:
            if lines.count(line) != 1:
                parser.error('missing or duplicate registration: ' + str(p) + ': ' + line)
    print(f'PASS: finite Z3 Galerkin overlap uniqueness; {len(THEOREMS)} theorems, {len(CHECKS)} audit probes')

if __name__ == '__main__':
    main()
