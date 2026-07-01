#!/usr/bin/env python3
"""合成 toehold RNA switch dynamic-range 序列码(第7模态:programmable RNA strand-displacement
device;single-mechanism, genuinely-novel;oracle 方向)。higher-order 序列是否在 composition +
hairpin 结构 proxy(代 ViennaRNA 物理 baseline)之上预测 cognate-trigger ON/OFF dynamic range,
且能 TRANSFER 到 held-out 来源 organism(leave-organism-out)?

y = winsorized log2(ON_OFF)(GSE149225 toehold MPRA)。baseline_comp = composition(mono/dinuc/GC/
length)。baseline_phys = comp + hairpin 结构 proxy(RC/stem-pairing density k4/5/6 + max-RC-stem;
toehold OFF-state hairpin 的 thermo 近似)。full = phys + higher-order(trinuc entropy, homopolymer/
AU/purine runs, palindrome density)。leave-ORGANISM-out(source_sequence 分组)holdout + perm。
主 verdict = higher-order over comp+hairpin-proxy(leave-organism-out)。作者报 thermo/kinetic
R²≈0.04-0.15, 序列 DNN R²≈0.43-0.70→序列有 thermo 之外信号, 但合成库 organism 泄漏必须控。
crosses_boundary / bounded_descriptor_only(只 interpolate 不跨 organism)/ composition_artifact。
NEW 模态 fresh contact, 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="toehold_switch_dynamic_range_gse149225"
CLAIM_ID="h3.cross_layer_relation.rna_strand_displacement_switch.toehold_dynamic_range_sequence_beyond_composition_hairpin_gse149225"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=250; N_MAX=8000; WINSOR=-8.0
random.seed(SEED)
COMP={"A":"T","T":"A","G":"C","C":"G"}
def revcomp(s): return "".join(COMP.get(c,"N") for c in reversed(s))

def _inv(M):
    n=len(M); A=[row[:]+[1.0 if i==j else 0.0 for j in range(n)] for i,row in enumerate(M)]
    for c in range(n):
        p=max(range(c,n),key=lambda r:abs(A[r][c]))
        if abs(A[p][c])<1e-12: A[p][c]+=1e-9
        A[c],A[p]=A[p],A[c]; pv=A[c][c]; A[c]=[v/pv for v in A[c]]
        for r in range(n):
            if r==c: continue
            f=A[r][c]
            if f: A[r]=[a-f*b for a,b in zip(A[r],A[c])]
    return [row[n:] for row in A]
def matvec(M,v): return [sum(a*b for a,b in zip(row,v)) for row in M]
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def zscols(rows):
    p=len(rows[0]); cols=list(zip(*rows)); out=[]
    for j in range(p):
        c=cols[j]; m=sum(c)/len(c); sd=(sum((x-m)**2 for x in c)/len(c))**0.5 or 1.0
        out.append([(x-m)/sd for x in c])
    return [list(r) for r in zip(*out)]
def prep(X, foldof, folds):
    n=len(X); p=len(X[0]); packs=[]
    for f in folds:
        tr=[i for i in range(n) if foldof[i]!=f]; te=[i for i in range(n) if foldof[i]==f]
        if not te or not tr: continue
        XtX=[[0.0]*p for _ in range(p)]
        for i in tr:
            xi=X[i]
            for a in range(p):
                xa=xi[a]
                if xa==0.0: continue
                row=XtX[a]
                for b in range(a,p): row[b]+=xa*xi[b]
        for a in range(p):
            for b in range(a): XtX[a][b]=XtX[b][a]
            XtX[a][a]+=RIDGE
        packs.append((_inv(XtX),[[X[i][a] for i in tr] for a in range(p)],tr,te,[X[i] for i in te]))
    return packs
def evalr2(packs, y):
    preds={}
    for Ainv,cols,tr,te,Xte in packs:
        ytr=[y[i] for i in tr]; w=matvec(Ainv,[dot(col,ytr) for col in cols])
        for j,i in enumerate(te): preds[i]=dot(Xte[j],w)
    idx=sorted(preds); yt=[y[i] for i in idx]; pr=[preds[i] for i in idx]
    m=sum(yt)/len(yt); sst=sum((v-m)**2 for v in yt) or 1.0
    return 1.0-sum((a-b)**2 for a,b in zip(yt,pr))/sst

def comp_feats(s):
    L=len(s); f={c:s.count(c)/L for c in "ACGT"}
    di={a+b:0 for a in "ACGT" for b in "ACGT"}
    for i in range(L-1):
        d=s[i:i+2]
        if d in di: di[d]+=1
    tot=L-1 or 1
    return [f["A"],f["C"],f["G"],f["G"]+f["C"],L/80.0]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def rc_density(s,k):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/len(ks) if ks else 0.0
def max_rc_stem(s,kmax=14):
    best=0
    for k in range(4,min(kmax,len(s)//2)+1):
        pos={}
        for i in range(len(s)-k+1): pos.setdefault(s[i:i+k],[]).append(i)
        found=False
        for km,ps in pos.items():
            rc=revcomp(km)
            if rc in pos and any(abs(pi-pj)>=k for pi in ps for pj in pos[rc]): found=True; break
        if found: best=k
        else: break
    return best
def hairpin_feats(s):
    return [rc_density(s,4),rc_density(s,5),rc_density(s,6),max_rc_stem(s)/14.0]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def mrun(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def palin_density(s,k=6):
    ks=[s[i:i+k] for i in range(len(s)-k+1)]
    if not ks: return 0.0
    return sum(1 for km in ks if km==revcomp(km))/len(ks)
def higher_feats(s):
    L=len(s)
    return [shannon_k(s,3), mrun(s,"A")/L, mrun(s,"T")/L, max(mrun(s,c) for c in "ACGT")/L,
            mrun(s,"AG")/L, mrun(s,"AT")/L, palin_density(s)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); Sall=D["switches"]; n_total=len(Sall)
    if n_total>N_MAX:
        idx=list(range(n_total)); random.Random(SEED).shuffle(idx)
        S=[Sall[i] for i in sorted(idx[:N_MAX])]
    else: S=Sall
    n=len(S)
    cores=[x["core"] for x in S]; y=[max(WINSOR,float(x["y"])) for x in S]
    Cf=[comp_feats(c) for c in cores]; Hp=[hairpin_feats(c) for c in cores]; Hi=[higher_feats(c) for c in cores]
    Xc=[[1.0]+r for r in zscols(Cf)]
    Xp=[[1.0]+r for r in zscols([Cf[i]+Hp[i] for i in range(n)])]                 # comp + hairpin-proxy(物理)
    Xf=[[1.0]+r for r in zscols([Cf[i]+Hp[i]+Hi[i] for i in range(n)])]           # + higher-order

    orgs=sorted(set(x["source"] for x in S)); ofold={o:i%FOLDS for i,o in enumerate(orgs)}
    fo_org=[ofold[x["source"]] for x in S]                                         # leave-organism-out
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS

    F=list(range(FOLDS))
    r2c=evalr2(prep(Xc,fo_org,F),y)
    pp=prep(Xp,fo_org,F); pf=prep(Xf,fo_org,F)
    r2p=evalr2(pp,y); r2f=evalr2(pf,y)
    incr_hairpin=r2p-r2c                                                           # 物理结构 over composition
    incr_higher=r2f-r2p                                                            # 主: higher-order over comp+hairpin, leave-org-out
    incr_higher_random=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xp,fo_rnd,F),y)      # interpolation 参照

    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pp,yp); nulls.append(ic)
        if ic>=incr_higher: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)

    floor=incr_higher>=0.01; sig=pval<0.05
    if floor and sig: verdict="crosses_boundary"
    elif incr_higher_random>=0.01 and not floor: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"

    checks={"n_switches_used":n,"n_total":n_total,"n_source_organisms":len(orgs),
            "r2_composition_leave_org_out":round(r2c,4),
            "r2_comp_plus_hairpin_leave_org_out":round(r2p,4),
            "r2_full_leave_org_out":round(r2f,4),
            "incr_hairpin_over_composition":round(incr_hairpin,4),
            "incr_higherorder_over_comp_hairpin_leave_org_out":round(incr_higher,4),
            "incr_higherorder_random_split":round(incr_higher_random,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order 序列在 composition + hairpin 物理 proxy 之上预测 toehold dynamic range, 且跨 held-out 来源 organism 迁移 -- 一个 thermo 之外、organism-可迁移的 switch 序列码" if verdict=="crosses_boundary"
                              else "higher-order 序列只在同 organism 内 interpolate, 不跨 held-out organism 迁移(来源特异/合成库泄漏), 非通用码" if verdict=="bounded_descriptor_only"
                              else "leave-organism-out 后 higher-order 序列不在 composition+hairpin proxy 之上加显著信号"),
            "framing":"NEW 模态 boundary-map contact(programmable RNA strand-displacement switch: 序列 higher-order -> cognate-trigger ON/OFF dynamic range, 超 composition+hairpin 物理 proxy, 跨-organism 迁移已测), 非新机制;物理 baseline=stem-pairing hairpin proxy(纯 stdlib 代 ViennaRNA)",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM,"winsor":WINSOR}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
