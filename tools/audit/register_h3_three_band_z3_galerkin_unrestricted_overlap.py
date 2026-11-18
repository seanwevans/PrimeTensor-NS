#!/usr/bin/env python3
"""Register unrestricted exact finite Leray-Galerkin initial-segment uniqueness."""
import argparse, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinUnrestrictedOverlap'
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3GalerkinFiniteODE_compactPaths_commonBall244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedUniqueOnIcc244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_unrestrictedOverlapUnique244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_differentEndsAgree244',
    'thirdFullThreeBand_z3GalerkinFiniteODE_longerSegment_extends244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(row for name in THEOREMS for row in (
    '#check ' + NS + name,
    '#print axioms ' + NS + name,
))

def add_missing(path, rows, prepend=False):
    original = path.read_text(encoding='utf-8')
    known = set(original.splitlines())
    missing = [r for r in rows if r not in known]
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
    for p in (source,root,audit):
        if not p.is_file(): parser.error('missing '+str(p))
    code = source.read_text(encoding='utf-8')
    scrub = re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub = re.sub(r'--[^\n]*', '', scrub)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', scrub):
        parser.error('unsafe or unproved assertion')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for n in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(n) + r'\b', code)) != 1:
            parser.error('missing or duplicate theorem '+n)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, CHECKS)
    for p,rows in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=p.read_text(encoding='utf-8').splitlines()
        for row in rows:
            if lines.count(row)!=1: parser.error('missing or duplicate registration '+str(p)+': '+row)
    print('PASS: 5 unrestricted overlap theorems and 10 audit probes')

if __name__ == '__main__': main()
