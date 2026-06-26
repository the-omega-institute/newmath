# Compression Preservation

- Claim status: `present-but-fail-closed`
- Failed gate: `H2-HG2`
- Task preserved: `true`
- Classifier agreement: `0.000000`
- Gap-head agreement: `1.000000`
- Ledger equivalence: `false`

## Hardgates

| gate | status | evidence pointer | evidence |
| --- | --- | --- | --- |
| H2-HG1 | `pass` | `$.arms.student_performance_distilled.task_preserved` | task accuracy remains within teacher tolerance |
| H2-HG2 | `fail` | `$.arms.student_performance_distilled.classifier_agreement` | independent classifier agreement is below the critical preservation floor |
| H2-HG3 | `fail` | `$.claimability.quality_preserving_compression_claimable` | quality-preserving compression requires task, classifier, gap-head, and ledger preservation |
| U-HG1 | `pass` | `$.evidence_refs.pointer_resolution.all_required_pointers_resolve` | all required evidence pointers resolve to non-null JSON cells |
| U-HG2 | `pass` | `$.reproducibility.byte_identical` | fixed-seed producer replay is byte-identical for committed artifacts |
| U-HG3 | `pass` | `$.schema_id` | claim capsule uses the unversioned schema id |
| U-HG4 | `pass` | `$.not_claimed` | not_claimed lists the required global and mechanism boundaries |
| U-HG5 | `pass` | `$.failed_gate` | any failed H2 or U row forces fail-closed claim status and failed_gate |
| U-HG6 | `pass` | `$.what_was_learned` | learning note names the classifier-preservation gap |
| U-HG7 | `pass` | `$.revocation.rows` | revocation rows cover pointer failure, regen drift, and classifier-agreement regression |
| U-HG8 | `pass` | `$.forbidden_claim_term_audit.hits` | forbidden full-scope positive claim term audit has zero hits |

## Not Claimed

- global model quality
- full LeJEPA reproduction
- full TensorNameCert
- LLM behavior quality
- mechanism closure unless D5-M gate passes
