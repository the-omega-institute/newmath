# New Model Hardgates

- Generated at: `2026-06-12T06:36:23.020151+00:00`
- Schema: `bedc-quality-lab:new-model-hardgates`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`

| gate | requirement | candidate pointer | evidence pointer | not claimed |
| --- | --- | --- | --- | --- |
| `NEW-MODEL-HG1` | semantic model_id is present, unique, and not satisfied by report_id | `$.hardgate_instances.NEW-MODEL-HG1` | `$.hardgate_instances.NEW-MODEL-HG1.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG1.not_claimed_pointer` |
| `NEW-MODEL-HG2` | complete architecture specification pointer | `$.hardgate_instances.NEW-MODEL-HG2` | `$.hardgate_instances.NEW-MODEL-HG2.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG2.not_claimed_pointer` |
| `NEW-MODEL-HG3` | complete training objective specification pointer | `$.hardgate_instances.NEW-MODEL-HG3` | `$.hardgate_instances.NEW-MODEL-HG3.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG3.not_claimed_pointer` |
| `NEW-MODEL-HG4` | ClaimCapsule pointer | `$.hardgate_instances.NEW-MODEL-HG4` | `$.hardgate_instances.NEW-MODEL-HG4.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG4.not_claimed_pointer` |
| `NEW-MODEL-HG5` | EvidenceEnvelope pointer | `$.hardgate_instances.NEW-MODEL-HG5` | `$.hardgate_instances.NEW-MODEL-HG5.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG5.not_claimed_pointer` |
| `NEW-MODEL-HG6` | CostProtocol pointer | `$.hardgate_instances.NEW-MODEL-HG6` | `$.hardgate_instances.NEW-MODEL-HG6.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG6.not_claimed_pointer` |
| `NEW-MODEL-HG7` | parameter-matched baseline pointer | `$.hardgate_instances.NEW-MODEL-HG7` | `$.hardgate_instances.NEW-MODEL-HG7.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG7.not_claimed_pointer` |
| `NEW-MODEL-HG8` | compute-matched baseline pointer | `$.hardgate_instances.NEW-MODEL-HG8` | `$.hardgate_instances.NEW-MODEL-HG8.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG8.not_claimed_pointer` |
| `NEW-MODEL-HG9` | matched-random structural control pointer | `$.hardgate_instances.NEW-MODEL-HG9` | `$.hardgate_instances.NEW-MODEL-HG9.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG9.not_claimed_pointer` |
| `NEW-MODEL-HG10` | at least three OOD or stress surface pointers | `$.hardgate_instances.NEW-MODEL-HG10` | `$.hardgate_instances.NEW-MODEL-HG10.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG10.not_claimed_pointer` |
| `NEW-MODEL-HG11` | learned UER reduction over matched-random pointer | `$.hardgate_instances.NEW-MODEL-HG11` | `$.hardgate_instances.NEW-MODEL-HG11.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG11.not_claimed_pointer` |
| `NEW-MODEL-HG12` | FalseLedgerRate non-regression pointer | `$.hardgate_instances.NEW-MODEL-HG12` | `$.hardgate_instances.NEW-MODEL-HG12.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG12.not_claimed_pointer` |
| `NEW-MODEL-HG13` | nondecreasing benefit pointer | `$.hardgate_instances.NEW-MODEL-HG13` | `$.hardgate_instances.NEW-MODEL-HG13.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG13.not_claimed_pointer` |
| `NEW-MODEL-HG14` | decreasing debt pointer | `$.hardgate_instances.NEW-MODEL-HG14` | `$.hardgate_instances.NEW-MODEL-HG14.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG14.not_claimed_pointer` |
| `NEW-MODEL-HG15` | quality_q confidence-interval low endpoint above zero pointer | `$.hardgate_instances.NEW-MODEL-HG15` | `$.hardgate_instances.NEW-MODEL-HG15.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG15.not_claimed_pointer` |
| `NEW-MODEL-HG16` | positive classifier_shift_count pointer | `$.hardgate_instances.NEW-MODEL-HG16` | `$.hardgate_instances.NEW-MODEL-HG16.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG16.not_claimed_pointer` |
| `NEW-MODEL-HG17` | no forbidden inference evidence pointer | `$.hardgate_instances.NEW-MODEL-HG17` | `$.hardgate_instances.NEW-MODEL-HG17.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG17.not_claimed_pointer` |
| `NEW-MODEL-HG18` | negative-witness sweep pass pointer | `$.hardgate_instances.NEW-MODEL-HG18` | `$.hardgate_instances.NEW-MODEL-HG18.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG18.not_claimed_pointer` |
| `NEW-MODEL-HG19` | MechanismNameCertCandidate at least partial pointer | `$.hardgate_instances.NEW-MODEL-HG19` | `$.hardgate_instances.NEW-MODEL-HG19.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG19.not_claimed_pointer` |
| `NEW-MODEL-HG20` | not_claimed pointer excludes universal architecture, production, and full closure claims | `$.hardgate_instances.NEW-MODEL-HG20` | `$.hardgate_instances.NEW-MODEL-HG20.evidence_pointer` | `$.hardgate_instances.NEW-MODEL-HG20.not_claimed_pointer` |
