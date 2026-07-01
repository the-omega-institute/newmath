#!/usr/bin/env python3
"""E. coli intrinsic terminator strength 序列码(第9模态:transcription termination;single-mechanism;
oracle 方向)。higher-order 序列是否在 composition + 作者 validated 物理模型(Predicted TS hairpin-
U-tract kinetic model + ∆G 组分)之上预测 terminator strength, identity-cluster-controlled? y=
log2(Average Strength)(Chen 2013 Nat Methods, 507 terminators 311 natural+196 synthetic, ~43nt)。
baseline_comp=composition(mono/dinuc/GC/len);baseline_phys=+Predicted TS + ∆GU/L/H/A(validated 物理);
full=+higher-order(RC/stem density, max-RC-stem, entropy, U-run/A-run)。identity-cluster(k-mer minhash)
+ leave-source(natural/synthetic) diagnostic + perm。作者物理模型 Pearson~0.64 中等→测 structure 是否超它。
crosses_boundary / bounded_descriptor_only / composition_artifact。NEW 模态 fresh contact 非新机制。纯 stdlib。"""
import json, math, random, pathlib, sys, zlib
from collections import Counter, defaultdict

EXPERIMENT_ID="terminator_intrinsic_strength_chen2013_nmeth2515"
CLAIM_ID="h3.cross_layer_relation.transcription_termination.intrinsic_terminator_strength_sequence_beyond_composition_physical_chen2013"
DATA_PATH=pathlib.Path.cwd()/("tools/bio_reality/data/"+EXPERIMENT_ID+".json")
SEED=20260701; RIDGE=1.0; FOLDS=5; PERM=400; KMER=8; JAC=0.5
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
    return [f["A"],f["C"],f["G"],f["G"]+f["C"],L/60.0]+[di[a+b]/tot for a in "ACGT" for b in "ACGT"]
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
def shannon_k(s,k):
    c=Counter(s[i:i+k] for i in range(len(s)-k+1)); n=sum(c.values()) or 1
    return -sum((v/n)*math.log((v/n),2) for v in c.values())
def mrun(s,al):
    b=c=0
    for ch in s:
        if ch in al: c+=1; b=max(b,c)
        else: c=0
    return b
def higher_feats(s):
    L=len(s)
    return [rc_density(s,4),rc_density(s,5),max_rc_stem(s)/14.0,shannon_k(s,3),mrun(s,"T")/L,mrun(s,"A")/L,max(mrun(s,c) for c in "ACGT")/L]

def kmer_set(s,k): return frozenset(s[i:i+k] for i in range(len(s)-k+1))
def minhash(ks,nh):
    out=[]
    for h in range(nh):
        mn=1<<32; salt=str(h).encode()
        for km in ks:
            v=zlib.crc32(salt+km.encode())&0xffffffff
            if v<mn: mn=v
        out.append(mn)
    return out
def clusters(seqs):
    n=len(seqs); ksets=[kmer_set(s,KMER) for s in seqs]; NH=16;BANDS=8;PB=2
    sigs=[minhash(k,NH) if k else [0]*NH for k in ksets]; par=list(range(n))
    def find(x):
        while par[x]!=x: par[x]=par[par[x]]; x=par[x]
        return x
    def uni(a,b):
        ra,rb=find(a),find(b)
        if ra!=rb: par[max(ra,rb)]=min(ra,rb)
    bk=defaultdict(list)
    for i in range(n):
        for band in range(BANDS): bk[(band,)+tuple(sigs[i][band*PB:(band+1)*PB])].append(i)
    for mem in bk.values():
        if len(mem)<2: continue
        for ai in range(len(mem)):
            i=mem[ai]; ki=ksets[i]
            if not ki: continue
            for bi in range(ai+1,len(mem)):
                j=mem[bi]; kj=ksets[j]
                if not kj or find(i)==find(j): continue
                if len(ki&kj)/len(ki|kj)>=JAC: uni(i,j)
    roots={}
    for i in range(n): roots.setdefault(find(i),len(roots))
    return [roots[find(i)] for i in range(n)]

def main():
    if not DATA_PATH.exists():
        print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"error","verdict":"needs_data","checks":{},"result":{"reason":"missing"}})); sys.exit(3)
    D=json.loads(DATA_PATH.read_text()); T=D["terminators"]; n=len(T)
    seqs=[x["seq"] for x in T]; y=[float(x["y"]) for x in T]
    def imp(key):
        vals=[x[key] for x in T if x.get(key) is not None]; med=sorted(vals)[len(vals)//2] if vals else 0.0
        return [x[key] if x.get(key) is not None else med for x in T]
    pts=imp("pred_ts"); pts=[math.log2(max(v,0.1)) for v in pts]
    dgu=imp("dgu"); dgl=imp("dgl"); dgh=imp("dgh"); dga=imp("dga")
    Cf=[comp_feats(s) for s in seqs]
    Phys=[[pts[i],dgu[i],dgl[i],dgh[i],dga[i]] for i in range(n)]
    Hf=[higher_feats(s) for s in seqs]
    Xc=[[1.0]+r for r in zscols(Cf)]
    Xp=[[1.0]+r for r in zscols([Cf[i]+Phys[i] for i in range(n)])]
    Xf=[[1.0]+r for r in zscols([Cf[i]+Phys[i]+Hf[i] for i in range(n)])]
    cl=clusters(seqs); ncl=len(set(cl)); big=max(Counter(cl).values())
    fo=[cl[i]%FOLDS for i in range(n)]; F=list(range(FOLDS))
    srcs=sorted(set(x["source"] for x in T)); sfold={s:i for i,s in enumerate(srcs)}; fo_src=[sfold[x["source"]] for x in T]

    r2c=evalr2(prep(Xc,fo,F),y); pp=prep(Xp,fo,F); pf=prep(Xf,fo,F)
    r2p=evalr2(pp,y); r2f=evalr2(pf,y)
    incr_phys=r2p-r2c; incr_higher=r2f-r2p
    incr_higher_src=evalr2(prep(Xf,fo_src,list(range(len(srcs)))),y)-evalr2(prep(Xp,fo_src,list(range(len(srcs)))),y)
    ge=0; nulls=[]; yidx=list(range(n))
    for _ in range(PERM):
        random.shuffle(yidx); yp=[y[i] for i in yidx]
        ic=evalr2(pf,yp)-evalr2(pp,yp); nulls.append(ic)
        if ic>=incr_higher: ge+=1
    pval=(ge+1)/(PERM+1); null_mean=sum(nulls)/len(nulls)
    floor=incr_higher>=0.01; sig=pval<0.05; transfers=incr_higher_src>=0.01
    if floor and sig and transfers: verdict="crosses_boundary"
    elif floor and sig: verdict="bounded_descriptor_only"
    else: verdict="composition_artifact"
    checks={"n_terminators":n,"n_natural":sum(1 for x in T if x["source"]=="natural"),"n_synthetic":sum(1 for x in T if x["source"]=="synthetic"),
            "n_identity_clusters":ncl,"largest_cluster":big,
            "r2_composition_ident":round(r2c,4),"r2_comp_plus_physicalmodel_ident":round(r2p,4),"r2_full_ident":round(r2f,4),
            "incr_physicalmodel_over_composition":round(incr_phys,4),
            "incr_higherorder_over_comp_physical_ident":round(incr_higher,4),
            "incr_higherorder_leave_source_out":round(incr_higher_src,4),
            "perm_null_mean_incr":round(null_mean,4),"perm_p":round(pval,4),
            "effect_floor_0.01":floor,"perm_sig_0.05":sig,"transfers_leave_source":transfers,"y_sd":round((sum((v-sum(y)/n)**2 for v in y)/n)**0.5,4)}
    result={"interpretation":("higher-order 序列在 composition + 作者物理模型(Predicted TS)之上预测 terminator strength, identity+leave-source 迁移 -- 物理模型之外的终止序列码" if verdict=="crosses_boundary"
                              else "higher-order 序列在物理模型之上加信号但不跨 natural/synthetic 迁移(库特异)" if (verdict=="bounded_descriptor_only")
                              else "identity-cluster holdout + perm 后 higher-order 序列不在 composition + 作者物理模型(hairpin-U-tract kinetic model)之上加显著信号"),
            "framing":"NEW 模态 boundary-map contact(sequence -> intrinsic transcription termination strength 超 composition + 作者 validated 物理模型), 非新机制",
            "data":D.get("source",""),"FOLDS":FOLDS,"PERM":PERM}
    print(json.dumps({"experiment_id":EXPERIMENT_ID,"claim_id":CLAIM_ID,"status":"ok","verdict":verdict,"checks":checks,"result":result},indent=1))
    sys.exit(0)

if __name__=="__main__": main()
