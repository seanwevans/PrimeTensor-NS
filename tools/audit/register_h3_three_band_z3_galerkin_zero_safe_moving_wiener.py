#!/usr/bin/env python3
"""Register zero-safe smooth moving-radius Galerkin Wiener derivative and audits."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
        'FullThirdSolenoidalKineticThreeBandZ3GalerkinZeroSafeMovingWiener')
NS='PrimeTensor.FirstMonomialTriad.'
DEFS=(
    'thirdFullThreeBandZ3SmoothAmplitude244',
    'thirdFullThreeBandZ3GalerkinSmoothWienerMass244',
    'thirdFullThreeBandZ3GalerkinSmoothWienerDerivative244',
)
THEOREMS=(
    'thirdFullThreeBand_z3SmoothAmplitude_pos244',
    'thirdFullThreeBand_z3Norm_le_smoothAmplitude244',
    'thirdFullThreeBand_z3SmoothAmplitude_le_norm_add244',
    'thirdFullThreeBand_z3WienerMass_le_smooth244',
    'thirdFullThreeBand_z3WienerDerivative_le_smooth244',
    'thirdFullThreeBand_z3SmoothWienerDerivative_nonneg244',
    'thirdFullThreeBand_z3SmoothWienerMass_le_true_add_error244',
    'thirdFullThreeBand_z3SmoothAmplitude_hasDerivAt244',
    'thirdFullThreeBand_z3SmoothDampedDerivative_le_source244',
    'thirdFullThreeBand_z3ZeroSafeMovingMode_hasDerivAt244',
    'thirdFullThreeBand_z3ZeroSafeMovingWiener_differential244',
    'thirdFullThreeBand_z3ZeroSafeMovingWiener_nonpos_on_ball244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for name in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+name,'#print axioms '+NS+name))


def add_missing(path, entries, prepend=False):
    old=path.read_text(encoding='utf-8')
    present=set(old.splitlines())
    missing=[line for line in entries if line not in present]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,
                        encoding='utf-8')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    flags=p.add_mutually_exclusive_group(required=True)
    flags.add_argument('--apply',action='store_true')
    flags.add_argument('--check',action='store_true')
    opts=p.parse_args()
    src=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'
    audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for path in (src,root,audit):
        if not path.is_file(): p.error('missing required file: '+str(path))
    code=src.read_text(encoding='utf-8')
    clean=re.sub(r'/-.*?-/', '', code, flags=re.S)
    clean=re.sub(r'--[^\n]*','',clean)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',clean):
        p.error('proof hole or new axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        p.error('trailing whitespace')
    for name in DEFS:
        if len(re.findall(r'(?m)^noncomputable def\s+'+re.escape(name)+r'\b',code))!=1:
            p.error('missing/repeated definition: '+name)
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',code))!=1:
            p.error('missing/repeated theorem: '+name)
    if opts.apply:
        add_missing(root,(IMPORT,))
        add_missing(audit,(IMPORT,),prepend=True)
        add_missing(audit,CHECKS)
    for path,expected in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=path.read_text(encoding='utf-8').splitlines()
        for row in expected:
            if lines.count(row)!=1:
                p.error('missing/duplicate registration: '+str(path)+' '+row)
    print(f'PASS: zero-safe moving Wiener: {len(DEFS)} defs, {len(THEOREMS)} theorems, {len(CHECKS)} trust probes')

if __name__=='__main__':
    main()
