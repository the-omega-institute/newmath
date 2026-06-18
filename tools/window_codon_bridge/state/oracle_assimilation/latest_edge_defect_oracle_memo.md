# Edge-Defect Oracle Memo

- schema: `window_codon_oracle_memo.v1`
- generated_ts: `2026-06-18T02:52:31Z`
- source_task_id: `2336e581-1091-4aaf-a6e0-b7f540a1c7e3`
- source_conversation_id: `conv_6139d5d7cea7ab03`
- oracle_response_chars: `6086`

## Strongest Mechanism

The strongest mechanism is Ser-codon-island-specific translational fidelity selection: UCN and AGY both encode Ser, but they expose the same intended Ser residue to different rare-error spectra. The selected variable is not speed, tRNA abundance, GC, codon-pair preference, mRNA folding, or ribosome dwell. It is the expression-weighted cost of the wrong amino acids occasionally inserted at that Ser site. The standard code really does split Ser between the UCN block and the AGY pair; NCBI’s standard code table lists Ser in both the TCN block and AGY positions, using DNA T where RNA would use U. NCBI The graph fact becomes biologically meaningful only if translation errors, mischarging errors, or near-cognate decoding errors are sufficiently local in codon space. If biology does not care about one-step neighborhoods, the missing Ser edge is just a graph curiosity. For Ser, the two islands have different error neighborhoods. UCN codons are one base away from Pro, Thr, Ala, Phe, Tyr, Cys, Leu, Trp, and, for UCA/UCG, Stop. AGY codons are one base away from Cys, Arg, Gly, Asn, Thr, and Ile. A synonymous UCN↔AGY change therefore preserves the intended Ser but changes the likely identities of mistranslated peptides. That is exactly the kind of mechanism that could make a missing Hamming-1 synonymous bridge matter. The route is:

## Decisive Confounders


## Sharpest Next Question

At matched Ser sites and matched expression context, does UCN↔AGY recoding change the peptide-resolved mistranslation spectrum in the direction predicted by the natural codon choice at highly expressed, functionally constrained Ser residues?
