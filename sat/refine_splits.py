#!/usr/bin/env python3
"""Refine timed-out orsplit leaves one level deeper: 3 edge-OR + all-negative."""
import glob, os, sys

def lits_of(path):
    return open(path).read().split() if os.path.exists(path) else []

def main():
    made=[]
    for r in glob.glob('runs/orsplit_*/*.res'):
        case=os.path.basename(r)[:-4]
        if 'TIMEOUT' not in open(r).read(): continue
        # skip if children already generated
        if os.path.exists(f'cubes/orig_replay_split/{case}r0.cube'): continue
        # locate its cube file: deeper cases carry their own name;
        # first-gen children use the parent's t-leaf cube name
        cf=f'cubes/orig_replay_split/{case}.cube'
        if not os.path.exists(cf):
            tag=case.replace('orsplit_','')
            parts=tag.split('_'); leaf=parts[0]; j=parts[1]
            cf=f'cubes/orig_replay_split/t{leaf}_{j}.cube'
        base=lits_of(cf)
        if not base: continue
        used={abs(int(l)) for l in base}
        # pick 3 free edges AFTER previously used ones — rotate window by depth
        depth=case.count('r')
        free=[e for e in range(1,232) if e not in used]
        pick=free[3*depth:3*depth+3] or free[:3]
        bl=' '.join(base)
        for k,e in enumerate(pick):
            out=f'cubes/orig_replay_split/{case}r{k}.cube'
            open(out,'w').write(bl+f' {e}\n'); made.append(out)
        out=f'cubes/orig_replay_split/{case}r3.cube'
        open(out,'w').write(bl+' '+' '.join(f'-{e}' for e in pick)+'\n'); made.append(out)
    with open('cases_orsplit2.txt','a') as f:
        for out in made:
            name=os.path.basename(out)[:-5]
            f.write(f'{name} 22 4 7 10 7 10 {out}\n')
    print('refined',len(made),'cubes ->',len(made)//4,'parents')

if __name__=='__main__': main()
