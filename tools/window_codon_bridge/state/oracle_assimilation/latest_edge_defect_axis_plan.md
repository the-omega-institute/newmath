# Edge-Defect Axis Oracle Assimilation

- schema: `window_codon_oracle_assimilation.v1`
- generated_ts: `2026-06-17T19:26:50Z`
- source_task_id: `5c26fa13-1a0f-44ae-ade4-787e7f38a955`
- source_conversation_id: `conv_6139d5d7cea7ab03`
- oracle_response_chars: `24251`

## Boundary

The oracle output is treated only as a generator of auditable 61-codon vectors. It cannot update claims or verdicts without deterministic local experiments.

## Execution Order

1. Implement the common projection harness first. Lock codon order, build  $C$ , implement residualization, implement  $u_{\rm SerSplit}$ , and implement the three exact nulls. Do this before constructing any new axis.
2. Run a synthetic negative-control axis pack. Generate random Gaussian vectors, GC-only vectors, wobble-only vectors, tAI-like vectors, and codon-pair-like vectors. Confirm that the harness rejects or residualizes them as expected.
3. Start with the matched-flank chemical lesion axis. It is the least vulnerable to the forbidden biological explanations. It also gives the cleanest interpretation of failure: either no independent residual or no SerSplit projection.
4. Then run DNA mutability and RNA modification/editing. These use existing finite databases and can be audited against GENCODE/gnomAD/RMBase-style fields. They are more confounded than the synthetic assay but still not translation-efficiency axes.
5. Only then run tRNA-body, aaRS, EF-Tu, and decoding-error routes. These are biologically closer to the Ser split but much more likely to collapse into tRNA supply, wobble, consensus loading, or dwell unless the exclusions are strict.

## Candidate Routes

### 1. Matched-flank chemical lesion residual axis

This is the cleanest non-translation route because the raw signal can be generated without tRNAs, ribosomes, codon usage, transcript abundance, or protein selection.

**Finite Data Source.** Synthesize a 61-oligo DNA panel and a 61-oligo RNA panel. Each oligo has identical flanking sequence and differs only in the central sense codon. Run fixed-condition chemical lesion assays: UV dimerization, oxidative damage, alkylation, deamination, and optionally ribose/backbone cleavage for RNA.

**Construction.** For each chemistry, estimate a lesion rate or hazard: $$x_{i,c}=\log\frac{\text{lesion}_{i,c}+1/2}{\text{molecules}_{i,c}+1}.$$ Normalize within chemistry and batch by z-score or batch random effect. Aggregate preregistered chemistries either separately or by inverse-variance mean. Residualize against  $C$  plus nearest-neighbor thermodynamic terms, CpG/UpA, purine/pyrimidine position indicators, and synthesis-QC covariates.

**Exclusion Controls.** Reject oligos with failed synthesis QC. Keep codon labels blinded until rates are frozen. Run scrambled-label negative controls. Repeat with at least two flank backgrounds to test whether any projection is flank-specific.

**Failure Mode.** Most of the signal may be base composition or nearest-neighbor chemistry. If residualization removes the vector, the route fails cleanly.

**Required Fields.** Codon, full oligo sequence, DNA/RNA flag, chemistry, exposure dose, time, buffer, temperature, molecule count, lesion count, readout method, replicate, batch, synthesis QC, purity, barcode, and blinded codon-label key.

### 2. Synonymous DNA damage/repair/mutability residual axis

This route uses natural genetic variation but aims to isolate codon-level mutability rather than selection or translation. gnomAD v4 is large enough to support rare-variant codon opportunity calculations; its v4 release reported 807,162 total individuals, split into exome and genome callsets aligned to GRCh38. GENCODE provides current human/mouse annotation releases and states its goal as identifying and classifying gene features with high accuracy based on biological evidence. gnomAD+1

**Finite Data Sources.** gnomAD rare synonymous SNVs, a de novo mutation catalog with callable masks, GENCODE or RefSeq CDS annotations, methylation/CpG tracks, replication timing, trinucleotide mutability model, local callability, and gene constraint annotations.

**Construction.** Count rare synonymous SNVs by reference codon per callable codon occurrence. Fit an expected neutral mutation model using noncoding or fourfold-degenerate sites: $$E[\text{SNV}]\sim \text{trinucleotide}+\text{methylation}+\text{strand}+\text{replication timing}+\text{callability}+\text{gene constraint}.$$ For each codon, compute a standardized residual burden: $$x_i=\frac{O_i-E_i}{\sqrt{E_i+\epsilon}}.$$ Residualize  $x$  against  $C$  plus CpG, UpA, trinucleotide opportunity, and methylation.

**Exclusion Controls.** Exclude splice-proximal, disease-enriched, low-callability, overlapping regulatory, RNA-editing, and repetitive regions. Repeat using de novo-only mutations. Repeat after removing CpG-containing codons.

**Failure Mode.** If GC/trinucleotide/CpG explains everything, the residual vanishes. If de novo-only data do not agree directionally with population rare variants, treat the axis as likely selection- or ascertainment-contaminated.

**Required Fields.** Codon, transcript ID, CDS coordinate, reference codon, alternate codon, synonymous consequence, allele count, allele number, callable opportunity, strand, local trinucleotide, methylation flag, replication timing, expression/callability, gene constraint, splice distance, regulatory-overlap flag.

### 3. Coding RNA editing and mRNA base-modification residual axis

This is a transcript-chemistry route. It is more biological than the synthetic lesion axis but still not a tRNA-supply, ramp, or dwell axis if handled carefully. RMBase v3.0 describes itself as integrating large epitranscriptome sequencing data and reports 73 RNA modification types across 62 species and 1,074,100 modification sites; RMBase v2 also documents modification-site, motif, RBP, and SNV-related modules. RNA Lab+1

**Finite Data Sources.** RMBase v3, m6A-Atlas/DirectRMDB if available, REDIportal/RADAR-style RNA-editing calls, GENCODE CDS annotation, matched RNA-seq coverage, tissue expression, mRNA half-life, local RNA structure, motif scores, RBP-density tracks, known DNA-variant masks.

**Construction.** Map high-confidence CDS events to codon identity. For each codon, compute an opportunity-normalized event burden: $$x_i=\operatorname{median}_{tissue,platform}\left[ \log\frac{\text{events}_{i}+1/2}{\text{callable expressed codon opportunities}_{i}+1} \right].$$ Build separate raw axes for A-to-I editing, C-to-U editing, m6A, m5C, pseudouridine, and a preregistered combined modification burden. Normalize within tissue/platform before codon aggregation. Residualize against  $C$  plus expression, editable-base opportunity, local motif, mRNA half-life, local structure, and RBP density.

**Exclusion Controls.** Remove known genomic SNPs, low-read-depth calls, mapping-ambiguous sites, repetitive regions, and sites not confidently in CDS. Run +1 and +2 shifted reading-frame pseudo-codon controls. Run tissue leave-one-out and platform leave-one-out audits.

**Failure Mode.** Very likely confounded by base motif and transcript structure. If the SerSplit projection survives only one tissue, one platform, or one modification caller, reject.

**Required Fields.** Transcript ID, genome coordinate, CDS coordinate, codon, codon position, modification/editing type, editing or modification level, coverage, confidence, tissue/cell type, platform, expression, local motif, strand, DNA-variant exclusion status, mRNA half-life, predicted local structure.

### 4. Genetic-code reassignment/lability residual axis

This route asks whether a standard-code sense codon has independently changed assignment across known or screened genetic codes after removing GC, codon disappearance, tRNA-loss, and wobble mechanisms. NCBI’s genetic-code table lists the standard code and alternative codes, gives a last-update date of September 23, 2024, and explains that its displayed tables use T rather than U for GenBank convention. ncbi.nlm.nih.gov

**Finite Data Sources.** NCBI Genetic Codes, Codetta or equivalent alternative-code genome screens, GTDB/NCBI taxonomy, genome-level codon-usage and GC summaries, tRNA-loss/wobble/codon-disappearance annotations where available.

**Construction.** Count phylogenetically deduplicated independent reassignment events per standard-code sense codon. Define opportunities as independent clades in which the codon is observable and assessable. Use a log-odds residual: $$x_i=\log\frac{\text{events}_i+1/2}{\text{opportunities}_i-\text{events}_i+1/2}.$$ Residualize against  $C$  plus degeneracy, stop-adjacency, codon disappearance, GC, domain/organelle flags, and mechanism annotations.

**Exclusion Controls.** Run with and without mitochondrial codes. Run bacterial/archaeal and eukaryotic nuclear subsets separately. Exclude stop-adjacent reassignments in a sensitivity test. Randomize event labels within matched degeneracy and GC classes.

**Failure Mode.** Reassignment events are sparse and often mechanistically tied to exactly the forbidden tRNA/wobble/codon-disappearance explanations. This route may fail by design after honest exclusions.

**Required Fields.** Codon, standard assignment, observed alternative assignment, code ID or genome ID, clade, organelle/nuclear status, evidence type, confidence, inferred mechanism, codon frequency, GC content, tRNA-loss flag, wobble-expansion flag, codon-disappearance score, phylogenetic deduplication ID.

### 5. Non-wobble tRNA body modification residual axis

This is the most natural translation-adjacent route, but it needs a hard firewall against tRNA supply and wobble. MODOMICS states that it provides information on modified ribonucleosides, biosynthetic pathways, modified residue locations in RNA sequences, and RNA-modifying enzymes, with download/API navigation and a 2025 update listed. iimcb.genesilico.pl

**Finite Data Sources.** MODOMICS modification-position records; GtRNAdb/tRNADB-CE/tRNAscan-SE tRNA gene and mature-sequence records; organism panel locked in advance; local codon-to-tRNA decoding map.

**Construction.** Remove anticodon bases 34, 35, 36 and remove any feature explicitly annotated as wobble-decoding. Encode only positions such as 32, 37, 38 and tRNA-body modification burden: binary presence, chemistry-class counts, enzyme-family counts, and evidence-weighted burden. Within each organism, z-score feature columns across tRNA isodecoders. Map tRNA records to codons by locked decoding rules. Aggregate isodecoders by median, organisms by robust median or random-effects mean, yielding a 61-vector  $x$ . Residualize against  $C$ .

**Exclusion Controls.** Leave-one-organism, leave-one-clade, leave-one-enzyme-family. Permute modification positions within tRNA bodies. Permute anticodon labels within amino-acid isotype. The negative controls must lose the SerSplit projection.

**Failure Mode.** If codon values are just tRNA supply, anticodon/wobble, or tRNA consensus in disguise, residualization will collapse the axis. This is a serious risk.

**Required Fields.** Organism, tRNA ID, amino-acid isotype, anticodon, decoded codon set, mature sequence, modification position, modification identity, chemistry class, enzyme, evidence type, abundance/gene-copy fields flagged as controls only.

### 6. aaRS charging-kinetics residual axis

This route is attractive because aminoacylation is not tRNA supply, codon usage, ramp, mRNA folding, or ribosome dwell. But codon-level resolution is hard because aminoacylation is measured on tRNA substrates, not codons. BRENDA’s current interface exposes enzyme fields including organism,  $K_M$ ,  $k_{cat}/K_M$ , pH, temperature, substrate, and turnover number; it also lists a 2026.1 release. BRENDA酶数据库

**Finite Data Sources.** BRENDA, SABIO-RK, primary-literature extraction, and a bounded fill-in panel if public coverage is incomplete.

**Construction.** Use only wild-type, full-length, cognate tRNA assays. Exclude anticodon mutants, minihelices, mischarging assays, and abundance proxies. Convert  $k_{cat}/K_M$  to  $\log_{10}$ . Within organism-aaRS-method blocks, subtract the amino-acid median and divide by MAD. Map tRNA substrates to codons using locked decoding rules; if one tRNA decodes multiple codons, either assign the same value to the decoded set with wobble controlled later, or mark the codons unresolved under a stricter policy. Aggregate by inverse-variance mean and residualize against  $C$ .

**Exclusion Controls.** Public-only versus fill-in-only split. Leave-one-aaRS-family. Leave-one-method. Reject if codon resolution relies only on anticodon/wobble assumptions.

**Failure Mode.** Full 61-codon codon-resolved kinetic coverage may not be available. If values are shared across wobble-decoded codons, the independent residual may be too weak or vanish.

**Required Fields.** aaRS identity, organism, tRNA substrate ID, amino acid, anticodon, decoded codon set, wild-type/mutant status, full-length versus minihelix, $k_{cat}$, $K_M$, $k_{cat}/K_M$, pH, temperature, buffer, assay method, replicate, source paper.

### 7. EF-Tu/EF1A charged-tRNA binding residual axis

This is parallel to aaRS kinetics but uses elongation-factor binding thermodynamics of charged tRNAs.

**Finite Data Sources.** Published EF-Tu/EF1A charged-tRNA binding measurements plus a bounded fill-in panel: one charged mature tRNA substrate per codon or per codon-resolvable decoding class, same elongation factor, same buffer.

**Construction.** Convert  $K_d$  to  $\Delta G=RT\ln K_d$ . Exclude uncharged tRNAs, minihelices, anticodon mutants, noncognate substrates, and wobble-engineered constructs. Within organism-factor-method block, subtract the amino-acid median. Map to codons, aggregate, residualize against  $C$ .

**Exclusion Controls.** Charged versus uncharged negative control. Buffer/method leave-one-out. Reject if residual values remain predictable from tRNA consensus or wobble class.

**Failure Mode.** Like aaRS kinetics, codon-level resolution may be weak. The route is useful only if mature charged-tRNA substrates are codon-resolvable after controls.

**Required Fields.** Organism, elongation factor, charged tRNA substrate, amino acid, anticodon, decoded codon set, modification state, charging state, $K_d$, $k_{\rm on}$, $k_{\rm off}$, $\Delta G$, temperature, buffer, replicate, assay method.

### 8. Matched decoding-error susceptibility residual axis

This is translation-adjacent, so it must be carefully separated from dwell and wobble. It should measure error susceptibility, not elongation speed.

**Finite Data Sources.** A bounded 61-codon reporter panel, or public dual-luciferase/fluorescence/mass-spec reporter assays if they use matched context. The bounded panel is cleaner: identical transcript, identical flanking codons, one variable A-site sense codon, basal condition only.

**Construction.** Estimate a codon-specific error probability: $$x_i=\operatorname{logit}\left(\frac{\text{error}_i+1/2}{\text{translated opportunities}_i+1}\right).$$ Normalize within reporter batch and subtract amino-acid median. Residualize against  $C$  plus near-cognate neighborhood composition.

**Exclusion Controls.** Exclude antibiotics, stress, starvation, or perturbation unless preregistered as separate axes. Swap flanking contexts. Permute codon labels within amino acid. Reject if near-cognate/wobble variables explain the residual.

**Failure Mode.** Decoding error is often mechanistically tied to wobble and tRNA abundance. The independence gate may correctly reject it.

**Required Fields.** Target codon, reporter construct, flanking sequence, organism/strain, condition, error class, near-cognate identities, read depth, translated-codon denominator, error count, replicate, batch, expression level, RNA abundance, protein abundance.

### 9. Synonymous MAVE/reporter fitness residual axis

This is lower priority because many public MAVE datasets do not cover all 61 codons evenly and are often confounded by mRNA stability or local sequence context. It becomes useful if paired with a bounded 61-codon synonymous reporter library. ProteinGym-style DMS benchmarks are large, but they primarily organize protein variant-effect assays rather than guaranteeing codon-balanced synonymous coverage. arXiv

**Finite Data Sources.** MaveDB/ProteinGym-style synonymous variants where available, plus a bounded codon-balanced synonymous reporter panel if public coverage is incomplete.

**Construction.** Extract only single-codon synonymous substitutions. Model score as: $$\text{score}\sim \text{gene}+\text{position}+\text{amino acid}+\text{source codon}+\text{target codon}+\text{assay}+\text{replicate}+\text{context covariates}.$$ Use the estimated target-codon effect as  $x_i$ . Residualize against  $C$  plus local RNA-structure and expression controls.

**Exclusion Controls.** Leave-one-gene, leave-one-assay, leave-one-library. Permute synonymous scores within amino acid and gene. Reject if one gene or one substitution direction carries the projection.

**Failure Mode.** Likely context-specific. This is a useful secondary route, not a first-pass route.

**Required Fields.** Gene, transcript, protein position, amino acid, reference codon, alternate synonymous codon, raw counts, normalized score, replicate, assay type, local codon context, RNA abundance, protein abundance, stability prediction, ribosome profiling if available as control only.

## Minimal Data Requests

- `Provide these tables in the locked 61-codon order`: 
- `sense_codons_61.tsv`: codon, amino acid, codon family, RNA spelling.
- `selection_packet_61.tsv`: d_perp_loading, f3_loading, optimal_loading, trna_consensus_loading, trna_supply_tai_centered_loading, trna_supply_tai_mean.
- `forbidden_controls_61.tsv`: GC1/2/3/total, CpG, UpA, wobble class, degeneracy, codon-pair in/out, mRNA-stability score, ribosome-dwell score.
- `projection_harness.py`: builds  $C$ , residualizes  $x$ , constructs  $u_{\rm SerSplit}$ , and returns exact within-Ser, sixfold-family, and matched-support p-values.

## Hard Rejection Rules

- Reject a route if any of the following occurs:
- Any of the 61 sense codons lacks a finite raw value after preregistered construction.
- The raw axis was constructed using the Stop/Ser edge-defect support,  $u_{\rm SerSplit}$ , q6_label, or q6_bits.
- Residual norm  $\|(I-P_C)x\|_2$  is near zero.
- A forbidden block predicts the residual under held-out audit.
- A route-specific negative control preserves at least 80% of  $|\rho|$  with the same sign.
- Projection exists only in one source, one clade, one tissue, one chemistry, one assay, or one batch.
- Exact projection survives only before GC/wobble/codon-pair/stability/dwell controls, not after.
- The most defensible first candidate is the matched-flank chemical lesion axis. The most biologically adjacent but highest-risk candidates are non-wobble tRNA-body modification, aaRS charging, and EF-Tu/EF1A binding. The exact projection test should be identical for all of them, so that the result is an audit ledger entry rather than a hand-tuned biological certificate.
