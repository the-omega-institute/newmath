#!/usr/bin/env python3
"""Phylogenetic-robustness test for the growth-rate-scaling crossing (claim 168).
Does partial Spearman(strength, log doubling | GC3, log tRNA) survive phylogenetic
structure? Tests: domain-stratified permutation null, drop-dominant-clade,
within-domain subsets, clade-aggregated. Pure stdlib, deterministic."""
import json, math, random, subprocess, pathlib

# Self-contained: run the registered experiment, extract per-organism partial data.
_REPO = pathlib.Path(__file__).resolve().parents[3] if "__file__" in dir() else pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath")
def _load_orgs():
    exp = _REPO / "tools/bio_reality/experiments/run_codon_abundance_crossing_strength_growth_rate_scaling.py"
    out = subprocess.run(["python3", str(exp)], cwd=str(_REPO), capture_output=True, text=True).stdout
    r = json.loads(out)["result"]
    orgs = []
    for o in r.get("organisms", []):
        if o.get("strength") is not None and o.get("doubling_time_min") is not None and o.get("gc3") is not None and o.get("trna_pool_total_copies"):
            orgs.append({"organism": o["organism"], "strength": o["strength"], "doubling": o["doubling_time_min"], "gc3": o["gc3"], "trna": o["trna_pool_total_copies"]})
    return orgs

ORGS = _load_orgs()

# Standard taxonomy (domain, phylum/clade) — curated, not fabricated.
TAX = {
 "bacillus_subtilis_subsp_subtilis_str_168": ("Bacteria","Firmicutes"),
 "escherichia_coli_k12_mg1655": ("Bacteria","Gammaproteobacteria"),
 "mycobacterium_smegmatis_str_mc2_155": ("Bacteria","Actinobacteria"),
 "campylobacter_jejuni_subsp_jejuni_nctc_11168": ("Bacteria","Campylobacterota"),
 "salmonella_enterica_serovar_typhimurium_lt2": ("Bacteria","Gammaproteobacteria"),
 "staphylococcus_aureus_nctc_8325": ("Bacteria","Firmicutes"),
 "mycobacterium_tuberculosis_h37rv": ("Bacteria","Actinobacteria"),
 "klebsiella_pneumoniae_mgh_78578": ("Bacteria","Gammaproteobacteria"),
 "sulfolobus_solfataricus": ("Archaea","Crenarchaeota"),
 "caenorhabditis_elegans": ("Eukaryote","Nematoda"),
 "danio_rerio": ("Eukaryote","Chordata"),
 "drosophila_melanogaster": ("Eukaryote","Arthropoda"),
 "gallus_gallus": ("Eukaryote","Chordata"),
 "homo_sapiens": ("Eukaryote","Chordata"),
 "mus_musculus": ("Eukaryote","Chordata"),
 "rattus_norvegicus": ("Eukaryote","Chordata"),
 "saccharomyces_cerevisiae": ("Eukaryote","Fungi"),
}

def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    r = [0.0]*len(xs); i = 0
    while i < len(xs):
        j = i
        while j+1 < len(xs) and xs[order[j+1]] == xs[order[i]]: j += 1
        avg = (i+j)/2.0 + 1
        for k in range(i, j+1): r[order[k]] = avg
        i = j+1
    return r

def ols_resid(y, X):
    # residual of y on columns X (list of rows) via normal equations
    n = len(y); p = len(X[0])
    XtX = [[sum(X[i][a]*X[i][b] for i in range(n)) for b in range(p)] for a in range(p)]
    Xty = [sum(X[i][a]*y[i] for i in range(n)) for a in range(p)]
    # solve XtX beta = Xty (Gaussian elimination)
    A = [row[:]+[Xty[k]] for k,row in enumerate(XtX)]
    for c in range(p):
        piv = max(range(c,p), key=lambda r: abs(A[r][c]))
        A[c],A[piv]=A[piv],A[c]
        if abs(A[c][c])<1e-12: continue
        for r in range(p):
            if r!=c:
                f=A[r][c]/A[c][c]
                for k in range(c,p+1): A[r][k]-=f*A[c][k]
    beta=[A[c][p]/A[c][c] if abs(A[c][c])>1e-12 else 0.0 for c in range(p)]
    return [y[i]-sum(beta[a]*X[i][a] for a in range(p)) for i in range(n)]

def pearson(a,b):
    n=len(a); ma=sum(a)/n; mb=sum(b)/n
    num=sum((a[i]-ma)*(b[i]-mb) for i in range(n))
    da=math.sqrt(sum((x-ma)**2 for x in a)); db=math.sqrt(sum((x-mb)**2 for x in b))
    return num/(da*db) if da>0 and db>0 else 0.0

def partial_spearman(subset, dt_override=None):
    s=[o["strength"] for o in subset]
    dt=[math.log(o["doubling"]) for o in (dt_override if dt_override else subset)] if dt_override else [math.log(o["doubling"]) for o in subset]
    gc=[o["gc3"] for o in subset]; tr=[math.log(o["trna"]) for o in subset]
    rs,rdt,rgc,rtr=ranks(s),ranks(dt),ranks(gc),ranks(tr)
    X=[[1.0,rgc[i],rtr[i]] for i in range(len(subset))]
    res_s=ols_resid(rs,X); res_d=ols_resid(rdt,X)
    return pearson(res_s,res_d)

# observed partial
obs=partial_spearman(ORGS)
n=len(ORGS)
print("n=%d  observed partial Spearman = %.4f"%(n,obs))

# domain composition
from collections import Counter
dom=Counter(TAX[o["organism"]][0] for o in ORGS)
phy=Counter(TAX[o["organism"]][1] for o in ORGS)
print("domains:",dict(dom),"| phyla:",dict(phy))

# (a) DOMAIN-STRATIFIED permutation: shuffle doubling within domain blocks
random.seed(20260630)
blocks={}
for i,o in enumerate(ORGS): blocks.setdefault(TAX[o["organism"]][0],[]).append(i)
B=20000; ge=0
dt_vals=[o["doubling"] for o in ORGS]
for _ in range(B):
    perm=dt_vals[:]
    for idxs in blocks.values():
        vals=[dt_vals[i] for i in idxs]; random.shuffle(vals)
        for k,i in enumerate(idxs): perm[i]=vals[k]
    shuffled=[{**ORGS[i],"doubling":perm[i]} for i in range(n)]
    if abs(partial_spearman(ORGS,dt_override=shuffled))>=abs(obs): ge+=1
p_strat=(1+ge)/(1+B)
print("(a) DOMAIN-stratified perm p = %.4f  (shuffle doubling within Bacteria/Archaea/Eukaryote)"%p_strat)

# (b) DROP dominant clade (Gammaproteobacteria)
for drop in ["Gammaproteobacteria","Actinobacteria"]:
    sub=[o for o in ORGS if TAX[o["organism"]][1]!=drop]
    print("(b) drop %-20s n=%d  partial = %.4f"%(drop,len(sub),partial_spearman(sub)))

# (c) within-domain subsets
for d in ["Bacteria","Eukaryote"]:
    sub=[o for o in ORGS if TAX[o["organism"]][0]==d]
    print("(c) %-10s only       n=%d  partial = %.4f"%(d,len(sub),partial_spearman(sub)))

# (d) clade-aggregated: mean strength & doubling per phylum, Spearman at clade level
agg={}
for o in ORGS:
    ph=TAX[o["organism"]][1]; agg.setdefault(ph,[]).append(o)
cl_s=[];cl_d=[]
for ph,os in agg.items():
    cl_s.append(sum(x["strength"] for x in os)/len(os)); cl_d.append(math.log(sum(x["doubling"] for x in os)/len(os)))
rs,rd=ranks(cl_s),ranks(cl_d)
print("(d) clade-aggregated Spearman (n_clades=%d) = %.4f"%(len(agg),pearson(rs,rd)))

def partial_controls(subset, controls):
    s=[o["strength"] for o in subset]; dt=[math.log(o["doubling"]) for o in subset]
    rs,rdt=ranks(s),ranks(dt)
    if not controls: return pearson(rs,rdt)
    X=[[1.0] for _ in subset]
    if "gc3" in controls:
        rg=ranks([o["gc3"] for o in subset])
        for i in range(len(subset)): X[i].append(rg[i])
    if "trna" in controls:
        rt=ranks([math.log(o["trna"]) for o in subset])
        for i in range(len(subset)): X[i].append(rt[i])
    return pearson(ols_resid(rs,X), ols_resid(rdt,X))

# (e) SEQUENTIAL partial (oracle overcontrol diagnostic): raw -> +GC3 -> +GC3+tRNA
print("\n=== (e) sequential partial Spearman(strength, logDT | controls) — overcontrol test ===")
for label,sub in [("ALL",ORGS),("Bacteria",[o for o in ORGS if TAX[o['organism']][0]=='Bacteria']),
                  ("Eukaryote",[o for o in ORGS if TAX[o['organism']][0]=='Eukaryote'])]:
    raw=partial_controls(sub,[]); g=partial_controls(sub,["gc3"]); gt=partial_controls(sub,["gc3","trna"])
    print("  %-10s n=%-2d  raw=%+.3f  +GC3=%+.3f  +GC3+tRNA=%+.3f"%(label,len(sub),raw,g,gt))

# (f) phylogenetic sign test: same-domain pairs with logDT ratio >=2x; faster -> higher strength?
print("=== (f) phylogenetic sign test (same-domain pairs, doubling ratio >=2x) ===")
for dom in ["Bacteria","Eukaryote"]:
    sub=[o for o in ORGS if TAX[o["organism"]][0]==dom]
    conc=0; tot=0
    for i in range(len(sub)):
        for j in range(i+1,len(sub)):
            a,b=sub[i],sub[j]
            if max(a["doubling"],b["doubling"])/min(a["doubling"],b["doubling"])<2.0: continue
            tot+=1
            faster, slower = (a,b) if a["doubling"]<b["doubling"] else (b,a)
            if faster["strength"]>slower["strength"]: conc+=1
    # two-sided binomial p (exact)
    from math import comb
    p=sum(comb(tot,k) for k in range(tot+1) if abs(k-tot/2)>=abs(conc-tot/2))/(2**tot) if tot>0 else 1.0
    print("  %-10s concordant(faster=stronger) %d/%d  binomial p=%.3f"%(dom,conc,tot,p))
