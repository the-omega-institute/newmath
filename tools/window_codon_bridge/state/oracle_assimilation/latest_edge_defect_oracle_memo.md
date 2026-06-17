# Edge-Defect Oracle Memo

- schema: `window_codon_oracle_memo.v1`
- generated_ts: `2026-06-17T14:09:17Z`
- source_task_id: `370152f2-4745-4899-a570-e0496623945b`
- source_conversation_id: `conv_6139d5d7cea7ab03`
- oracle_response_chars: `8159`

## Strongest Mechanism

The strongest route is codon-island-specific translational fidelity selection: UCN-Ser and AGY-Ser give the same intended amino acid, but they expose a Ser residue to different one-step error neighborhoods and different Ser-tRNA decoding channels. The selectable variable is not speed, abundance, GC, wobble, or folding; it is the expected cost of rare wrong protein products. The standard code really does encode Ser in two disconnected blocks: the UCN quartet and the AGY pair, as read from the standard translation table. NCBI’s standard code table lists the full 64-codon assignment for transl_table=1; in RNA notation, that assignment contains Ser at UCU/UCC/UCA/UCG and AGU/AGC. 国家生物技术信息中心 The graph fact matters only if biology cares about one-step errors. Ribosomes do not literally wander on an abstract Hamming graph, so the graph alone is not evidence. But translational errors are exactly the kind of process that can make one-base neighborhoods relevant: errors can arise from wrong codon–tRNA pairing or from wrong aminoacylation, and reported misincorporation rates are often estimated around  $10^{-5}$  to  $10^{-3}$  per codon depending on conditions. 维基百科 The mechanism would be this. At a given Ser site, the intended product is identical whether the codon is UCN or AGY. But the wrong products are not identical. UCN codons have one-step neighbors leading into amino acids such as Pro, Ala, Thr, Phe, Tyr, Cys, Leu, Trp, and for UCA/UCG, Stop. AGY codons have a different neighborhood, including Arg, Gly, Asn, Thr, Ile, and Cys. Therefore, a synonymous UCN↔AGY choice can change the distribution of mistranslated peptides while leaving the intended amino-acid sequence unchanged. That becomes a plausible expression-level pressure because highly expressed proteins generate many translation events. Even a rare codon-specific error can create many aberrant molecules if the gene is highly translated. Selection need not care about the average codon speed; it can care about whether the rare error product is toxic, aggregation-prone, dominant-negative, catalytically misleading, or disruptive at a conserved site. The relevant quantity is something like:

## Decisive Confounders


## Sharpest Next Question

At matched Ser sites and matched expression context, does UCN↔AGY recoding change the peptide-resolved mistranslation spectrum in the direction predicted by the natural codon choice at highly expressed, functionally constrained Ser residues?
