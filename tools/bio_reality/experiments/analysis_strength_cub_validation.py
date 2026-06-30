#!/usr/bin/env python3
"""Strength-validity check for the growth-rate-scaling crossing (claim 168):
does the per-organism crossing STRENGTH track an INDEPENDENT, reference-free
codon-usage-bias magnitude (Wright 1990 ENC) computed from the same CDS? If
strength rises as ENC falls (more bias), strength genuinely captures
translational-selection codon bias, not arbitrary codon-block predictiveness.
Pure stdlib, deterministic, self-contained (runs the registered experiment)."""
import json, math, subprocess, pathlib

_REPO = pathlib.Path(__file__).resolve().parents[3] if "__file__" in dir() else pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath")

CODON_AA = {}
for codons, aa in [
    ("TTT TTC","F"),("TTA TTG CTT CTC CTA CTG","L"),("ATT ATC ATA","I"),("ATG","M"),
    ("GTT GTC GTA GTG","V"),("TCT TCC TCA TCG AGT AGC","S"),("CCT CCC CCA CCG","P"),
    ("ACT ACC ACA ACG","T"),("GCT GCC GCA GCG","A"),("TAT TAC","Y"),("CAT CAC","H"),
    ("CAA CAG","Q"),("AAT AAC","N"),("AAA AAG","K"),("GAT GAC","D"),("GAA GAG","E"),
    ("TGT TGC","C"),("TGG","W"),("CGT CGC CGA CGG AGA AGG","R"),("GGT GGC GGA GGG","G"),
    ("TAA TAG TGA","*")]:
    for c in codons.split(): CODON_AA[c] = aa
FAMILIES = {}
for c, aa in CODON_AA.items():
    if aa != "*": FAMILIES.setdefault(aa, []).append(c)
DEG = {2: [aa for aa,cs in FAMILIES.items() if len(cs)==2],
       3: [aa for aa,cs in FAMILIES.items() if len(cs)==3],
       4: [aa for aa,cs in FAMILIES.items() if len(cs)==4],
       6: [aa for aa,cs in FAMILIES.items() if len(cs)==6]}

def enc_from_counts(codon_counts):
    Fbar = {}
    for deg, aas in DEG.items():
        Fs = []
        for aa in aas:
            cs = [codon_counts.get(c, 0) for c in FAMILIES[aa]]
            n = sum(cs)
            if n < 2: continue
            p2 = sum((c/n)**2 for c in cs)
            F = (n*p2 - 1)/(n - 1)
            if F > 0: Fs.append(F)
        if Fs: Fbar[deg] = sum(Fs)/len(Fs)
    if 3 not in Fbar and 2 in Fbar and 4 in Fbar:
        Fbar[3] = (Fbar[2] + Fbar[4]) / 2
    if not all(d in Fbar for d in (2,3,4,6)): return None
    enc = 2 + 9/Fbar[2] + 1/Fbar[3] + 5/Fbar[4] + 3/Fbar[6]
    return min(enc, 61.0)

def agg_codon_counts(organism):
    p = _REPO / ("tools/bio_reality/data/cds_codon_abundance_" + organism + ".json")
    if not p.exists(): return None
    d = json.loads(p.read_text())
    agg = {}
    for r in d.get("joined", []):
        for c, n in (r.get("codon_counts") or {}).items():
            agg[c] = agg.get(c, 0) + n
    return agg

def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i]); r=[0.0]*len(xs); i=0
    while i < len(xs):
        j=i
        while j+1<len(xs) and xs[order[j+1]]==xs[order[i]]: j+=1
        for k in range(i,j+1): r[order[k]]=(i+j)/2.0+1
        i=j+1
    return r
def pearson(a,b):
    n=len(a); ma=sum(a)/n; mb=sum(b)/n
    num=sum((a[i]-ma)*(b[i]-mb) for i in range(n))
    da=math.sqrt(sum((x-ma)**2 for x in a)); db=math.sqrt(sum((x-mb)**2 for x in b))
    return num/(da*db) if da>0 and db>0 else 0.0
def spearman(a,b): return pearson(ranks(a),ranks(b))

if __name__ == "__main__":
    exp = _REPO / "tools/bio_reality/experiments/run_codon_abundance_crossing_strength_growth_rate_scaling.py"
    out = subprocess.run(["python3", str(exp)], cwd=str(_REPO), capture_output=True, text=True).stdout
    orgs = json.loads(out)["result"]["organisms"]
    rows = []
    for o in orgs:
        if o.get("strength") is None: continue
        cc = agg_codon_counts(o["organism"])
        if not cc: continue
        enc = enc_from_counts(cc)
        if enc is None: continue
        rows.append((o["organism"], o["strength"], enc, o.get("doubling_time_min"), o.get("trna_pool_total_copies")))
    print("=== per-organism strength vs ENC (Wright effective number of codons) ===")
    for nm,s,e,dt,tr in sorted(rows, key=lambda r: r[2]):
        print("  %-44s strength=%.3f  ENC=%.1f"%(nm,s,e))
    strengths=[r[1] for r in rows]; encs=[r[2] for r in rows]
    print("\nn=%d"%len(rows))
    print("Spearman(strength, ENC)        = %+.3f   (NEGATIVE expected: lower ENC = more bias = stronger crossing)"%spearman(strengths,encs))
    # tRNA-pool cross-check (subset with tRNA)
    sub=[r for r in rows if r[4]]
    if sub:
        print("Spearman(strength, tRNA-pool)  = %+.3f   (n=%d; POSITIVE expected: more tRNA genes = stronger selection)"%(spearman([r[1] for r in sub],[math.log(r[4]) for r in sub]),len(sub)))
        print("Spearman(ENC, tRNA-pool)       = %+.3f   (n=%d; NEGATIVE expected: more tRNA = more bias = lower ENC)"%(spearman([r[2] for r in sub],[math.log(r[4]) for r in sub]),len(sub)))
