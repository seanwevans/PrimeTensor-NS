#!/usr/bin/env python3
"""Register the strong Galerkin ODE-to-retarded-Duhamel mathematical bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalKineticThreeBandZ3GalerkinODEToDuhamel'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullThreeBand_z3HeatIntegratingFactor_hasDerivAt244',
    'thirdFullThreeBand_z3HeatODE_retardedDuhamel244',
    'thirdFullThreeBand_z3GalerkinStrongODE_Duhamel244',
    'thirdFullThreeBand_z3GalerkinStrongODE_Residual25750000_100Ball244',
    'thirdFullThreeBand_z3GalerkinStrongODE_fullResidual25750000_100Ball244',
)
IMPORT = 'import ' + MODULE
PROBES = tuple(line for name in THEOREMS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def add_missing(path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    have = set(old.splitlines())
    missing = [x for x in entries if x not in have]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,
                        encoding='utf-8')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply', action='store_true')
    g.add_argument('--check', action='store_true')
    args = p.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            p.error('missing required ' + str(path))
    code = source.read_text(encoding='utf-8')
    clean = re.sub(r'/-.*?-/', '', code, flags=re.S)
    clean = re.sub(r'--[^\n]*', '', clean)
    if re.search(r'\b(?:sorry|admit|axiom)\b', clean):
        p.error('forbidden placeholder or axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        p.error('trailing whitespace')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b', code)) != 1:
            p.error('missing/duplicate theorem ' + name)
    if args.apply:
        add_missing(root, (IMPORT,))
        add_missing(audit, (IMPORT,), prepend=True)
        add_missing(audit, PROBES)
    for path, expected in ((root,(IMPORT,)), (audit,(IMPORT,*PROBES))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                p.error('missing/duplicate registration '+str(path)+' '+line)
    print(f'PASS: strong Galerkin ODE-to-Duhamel: '
          f'{len(THEOREMS)} theorems, {len(PROBES)} trust probes')

if __name__ == '__main__':
    main()
