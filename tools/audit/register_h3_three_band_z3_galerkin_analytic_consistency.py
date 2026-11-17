#!/usr/bin/env python3
"""Register actual-lattice three-radius Galerkin consistency gates."""
from pathlib import Path
import argparse, re, sys

sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[2]
MODULE=('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
 'FullThirdSolenoidalKineticThreeBandZ3GalerkinAnalyticConsistency')
NS='PrimeTensor.FirstMonomialTriad.'
DEFS=(
 'thirdFullThreeBandZ3NatDegree244',
 'thirdFullThreeBandZ3GalerkinLocalConsistencyCap244',
)
THEOREMS=(
 'thirdFullThreeBand_z3Degree_eq_natCast244',
 'thirdFullThreeBand_z3Weight_log_eq_pow244',
 'thirdFullThreeBand_z3TwoRadiusDerivativeEnvelope244',
 'thirdFullThreeBand_z3TwoRadiusLaplacianEnvelope244',
 'thirdFullThreeBand_z3ThreeRadiusDerivativeEnvelope244',
 'thirdFullThreeBand_z3ThreeRadiusLaplacianEnvelope244',
 'thirdFullThreeBand_z3WienerMass_radius_mono244',
 'thirdFullThreeBand_z3WienerDerivative_reserved244',
 'thirdFullThreeBand_z3PolarizedSource_mass_bound244',
 'thirdFullThreeBand_z3SourceDifference_twoRadius244',
 'thirdFullThreeBand_z3SourceDifference_100Ball244',
 'thirdFullThreeBand_z3GalerkinLocalConsistencyCoefficient244',
 'thirdFullThreeBand_z3GalerkinExplicitOmeshBudget244',
)
IMPORT='import '+MODULE
CHECKS=tuple(line for n in (*DEFS,*THEOREMS)
             for line in ('#check '+NS+n,'#print axioms '+NS+n))

def add_missing(path,entries,prepend=False):
 old=path.read_text(encoding='utf-8'); present=set(old.splitlines())
 missing=[line for line in entries if line not in present]
 if missing:
  block='\n'.join(missing)+'\n'
  path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
 p=argparse.ArgumentParser(description=__doc__)
 mode=p.add_mutually_exclusive_group(required=True)
 mode.add_argument('--apply',action='store_true')
 mode.add_argument('--check',action='store_true')
 args=p.parse_args()
 src=ROOT/(MODULE.replace('.','/')+'.lean')
 root=ROOT/'PrimeTensor.lean';audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
 for path in (src,root,audit):
  if not path.is_file():p.error('missing file: '+str(path))
 code=src.read_text(encoding='utf-8')
 stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('proof hole/new axiom')
 if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
 for kw,names in (('def',DEFS),('theorem',THEOREMS)):
  for name in names:
   if len(re.findall(r'(?m)^'+kw+r'\s+'+re.escape(name)+r'\b',code))!=1:
    p.error('missing/repeated '+kw+' '+name)
 if args.apply:
  add_missing(root,[IMPORT]);add_missing(audit,[IMPORT],prepend=True)
  add_missing(audit,CHECKS)
 for path,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
  ls=path.read_text(encoding='utf-8').splitlines()
  for line in required:
   if ls.count(line)!=1:p.error('missing/duplicate registration: '+str(path)+' '+line)
 print(f'PASS: three-radius Z3 Galerkin consistency: {len(THEOREMS)} theorems, '
       f'{len(DEFS)} definitions, {len(CHECKS)} trust probes')

if __name__=='__main__':main()
