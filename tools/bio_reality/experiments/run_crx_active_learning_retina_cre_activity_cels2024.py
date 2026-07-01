#!/usr/bin/env python3
"""CRX-dependent developing-retina CRE (enhancer/silencer) reporter activity 序列码(第10模态:
DNA cis-regulatory element reporter activity;single-mechanism;oracle 方向)。higher-order 序列结构
是否在 composition(mono/dinuc/GC)之上预测 MPRA reporter activity, 谱系-leakage-controlled?
y=expression_log2(Friedman/Cohen Cell Systems 2024, barakcohenlab/CRX-Active-Learning; 164bp)。
baseline_comp=composition;full=+higher-order 通用结构(k-mer 熵 k3/k4、reverse-complement/回文密度
k4/k5/k6、max-RC-stem、homopolymer/purine/AT run、CpG O/E)。leave-parent-family-out(original_seq,
突变衍生近重复整族 holdout)+ leave-library-out(generator 批次迁移)+ random-split 对照 + perm。
两因子规则:164bp 长 + 无强物理模型 → 预测 structure 跨界(POSITIVE)。
crosses_boundary / bounded_descriptor_only / composition_artifact。NEW 模态 fresh contact 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys
from collections import Counter, defaultdict

EXPERIMENT_ID="crx_active_learning_retina_cre_activity_cels2024"
CLAIM_ID="h3.cross_layer_relation.dna_cis_regulatory_element.crx_retina_cre_reporter_activity_sequence_beyond_composition_cels2024"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=300
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
            fx=A[r][c]
            if fx: A[r]=[a-fx*b for a,b in zip(A[r],A[c])]
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
    return [f["A"],f["C"],f["G"],f["G"]+f["C"]]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def rc_density(s,k):
    ks=set(s[i:i+k] for i in range(len(s)-k+1))
    return sum(1 for km in ks if revcomp(km) in ks)/len(ks) if ks else 0.0
def max_rc_stem(s,kmax=16):
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
def mrun(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def cpg_oe(s):
    L=len(s); cg=sum(1 for i in range(L-1) if s[i:i+2]=="CG")
    pc=s.count("C")/L; pg=s.count("G")/L
    exp=pc*pg*(L-1)
    return (cg/exp) if exp>0 else 0.0
def higher_feats(s):
    L=len(s)
    return [shannon_k(s,3), shannon_k(s,4), rc_density(s,4), rc_density(s,5), rc_density(s,6),
            max_rc_stem(s)/16.0, max(mrun(s,c) for c in "ACGT")/L, mrun(s,"AG")/L, mrun(s,"AT")/L, cpg_oe(s)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing %s"%DATA_PATH}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); E=D["elements"]; n=len(E)
    seqs=[x["seq"] for x in E]; y=[float(x["y"]) for x in E]
    fam=[x["fam"] for x in E]; libs=[x["library"] for x in E]
    Cf=[comp_feats(s) for s in seqs]; Hf=[higher_feats(s) for s in seqs]
    Xc=[[1.0]+r for r in zscols(Cf)]
    Xf=[[1.0]+r for r in zscols([Cf[i]+Hf[i] for i in range(n)])]
    # leave-parent-family-out folds
    fo_par=[fam[i]%FOLDS for i in range(n)]; F=list(range(FOLDS))
    # random-split 对照
    rnd=list(range(n)); random.Random(SEED).shuffle(rnd); fo_rnd=[0]*n
    for k,i in enumerate(rnd): fo_rnd[i]=k%FOLDS
    # leave-library-out folds
    ulib=sorted(set(libs)); lmap={l:i for i,l in enumerate(ulib)}; fo_lib=[lmap[l] for l in libs]

    pc_par=prep(Xc,fo_par,F); pf_par=prep(Xf,fo_par,F)
    r2c=evalr2(pc_par,y); r2f=evalr2(pf_par,y); incr_par=r2f-r2c
    incr_rnd=evalr2(prep(Xf,fo_rnd,F),y)-evalr2(prep(Xc,fo_rnd,F),y)
    Flib=list(range(len(ulib)))
    incr_lib=evalr2(prep(Xf,fo_lib,Flib),y)-evalr2(prep(Xc,fo_lib,Flib),y)
    # perm null on parent-grouped incr(复用 prep)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf_par,yp)-evalr2(pc_par,yp); nulls.append(ic)
        if ic>=incr_par: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_par>=0.01; sig=pval<0.05; transfers=incr_lib>=0.01
    if floor and sig and transfers: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"
    checks={"n_used":n,"n_total":D.get("n_total"),"n_families_total":D.get("n_families_total"),
            "n_families_used":len(set(fam)),"n_libraries":len(ulib),
            "r2_composition_parentfold":round(r2c,4),"r2_full_parentfold":round(r2f,4),
            "incr_higherorder_parentfamily_holdout":round(incr_par,4),
            "incr_higherorder_random_split":round(incr_rnd,4),
            "incr_higherorder_leave_library_out":round(incr_lib,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"transfers_leave_library":transfers,
            "y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order 序列结构在 composition 之上预测 CRX CRE reporter activity, 谱系-holdout + 跨 generator library 迁移 -- composition 之外真实的 CRE 序列码" if verdict=="crosses_boundary"
                              else "higher-order 结构在谱系-holdout 上超 composition 且显著, 但不跨 generator library 迁移(库特异 grammar)" if verdict=="bounded_descriptor_only"
                              else "leave-parent-family holdout + perm 后 higher-order 通用结构不在 composition 之上加显著信号(CRE activity 由 composition/motif-composition 主导)"),
            "framing":"NEW 模态 boundary-map contact(DNA cis-regulatory element 序列 higher-order -> CRX 视网膜 CRE reporter activity 超 composition), 非新机制; 两因子规则(164bp 长 + 无强物理模型)预测点",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
