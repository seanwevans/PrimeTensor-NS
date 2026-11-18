#!/usr/bin/env python3
"""Register canonical Z3 Galerkin segment supremum and common-horizon existence."""
import argparse, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[2]
MODULE='PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3GalerkinSupremumFlow'
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=('thirdFullThreeBand_z3GalerkinStrongSegment_nonempty244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_agrees244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_initial244', 'thirdFullThreeBand_z3GalerkinCanonicalUnion_strong244', 'thirdFullThreeBand_z3GalerkinCommonHorizon_gt244', 'thirdFullThreeBand_z3GalerkinCappedEndpoints_nonempty244', 'thirdFullThreeBand_z3GalerkinCappedEndpoints_bddAbove244', 'thirdFullThreeBand_z3GalerkinCappedSup_start_lt244', 'thirdFullThreeBand_z3GalerkinCappedSup_le_horizon244', 'thirdFullThreeBand_z3GalerkinReachable_belowCappedSup244', 'thirdFullThreeBand_z3GalerkinCappedSup_eq_horizon244', 'thirdFullThreeBand_z3GalerkinFiniteODE_exists_commonHorizon244')
DEFINITIONS=('thirdFullThreeBandZ3GalerkinBaseSegment244', 'thirdFullThreeBandZ3GalerkinReachable244', 'thirdFullThreeBandZ3GalerkinCanonicalUnion244', 'thirdFullThreeBandZ3GalerkinCommonHorizon244', 'thirdFullThreeBandZ3GalerkinCappedEndpoints244', 'thirdFullThreeBandZ3GalerkinCappedSup244')
STRUCTURES=('thirdFullThreeBandZ3GalerkinStrongSegment244',)
IMPORT='import '+MODULE
CHECKS=tuple(row for n in (*THEOREMS,*DEFINITIONS,*STRUCTURES) for row in (
    '#check '+NS+n, '#print axioms '+NS+n))

def add_missing(path,rows,prepend=False):
    original=path.read_text(encoding='utf-8')
    known=set(original.splitlines())
    missing=[r for r in rows if r not in known]
    if missing:
        block='\n'.join(missing)+'\n'
        path.write_text(block+original if prepend else original.rstrip('\n')+'\n'+block,
                        encoding='utf-8')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply',action='store_true')
    group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    source=ROOT/(MODULE.replace('.','/')+'.lean')
    root=ROOT/'PrimeTensor.lean'
    audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for p in (source,root,audit):
        if not p.is_file(): parser.error('missing '+str(p))
    code=source.read_text(encoding='utf-8')
    scrub=re.sub(r'/-.*?-/', '', code, flags=re.S)
    scrub=re.sub(r'--[^\n]*','',scrub)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',scrub):
        parser.error('unproved or unsafe source')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    for n in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(n)+r'\b',code))!=1:
            parser.error('missing/duplicate theorem '+n)
    for n in DEFINITIONS:
        if len(re.findall(r'(?m)^(?:noncomputable )?def\s+'+re.escape(n)+r'\b',code))!=1:
            parser.error('missing/duplicate definition '+n)
    for n in STRUCTURES:
        if len(re.findall(r'(?m)^structure\s+'+re.escape(n)+r'\b',code))!=1:
            parser.error('missing/duplicate structure '+n)
    if args.apply:
        add_missing(root,(IMPORT,))
        add_missing(audit,(IMPORT,),prepend=True)
        add_missing(audit,CHECKS)
    for p,rows in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
        lines=p.read_text(encoding='utf-8').splitlines()
        for row in rows:
            if lines.count(row)!=1: parser.error('missing/duplicate registration '+str(p)+': '+row)
    print('PASS: '+str(len(THEOREMS))+' Z3 supremum theorems and '+str(len(CHECKS))+' audit probes')

if __name__=='__main__': main()
