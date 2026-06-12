# Mechanism DNA

- Schema: `bedc-quality-lab:mechanism-dna`
- Artifact: `bedc-quality-lab:mechanism-dna`
- Hardgate: `pass`

| row | mechanism | component | causal path | intervention | ablation | negative witness | status |
| --- | --- | --- | --- | --- | --- | --- | --- |
`gap-head-attribution-capsule` | `gap-head-residualized-attribution` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_case` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `reports/canonical/gap_head_attribution_capsule.json:$.head_channel_patch_evidence.causal_patch_claim` | `reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.head_causal_patch` | `reports/canonical/gap_head_attribution_capsule.json:$.negative_witness[0]` | `pass`
`discovery-regularized-training` | `training-mechanism-certificate` | `reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert` | `reports/canonical/discovery-regularized-training.json:$.training_loop_trace` | `reports/canonical/discovery-regularized-training.json:$.torch_training_evidence` | `reports/canonical/discovery-regularized-training.json:$.mechanism_ablation.status` | `reports/canonical/discovery-regularized-training.json:$.negative_witness_mutations` | `pass`
`mechanism-seeking-network` | `distinction-module-mechanism` | `reports/canonical/mechanism-seeking-network.json:$.mechanism_gate_summary.by_mechanism` | `reports/canonical/mechanism-seeking-network.json:$.distinction_module_evidence` | `reports/canonical/mechanism-seeking-network.json:$.distinction_module_evidence.records[0].patch_rows_pointer` | `reports/canonical/mechanism-seeking-network.json:$.distinction_module_evidence.records[0].ablation_rows_pointer` | `reports/canonical/mechanism-seeking-network.json:$.revocation_rows` | `pass`
`discovery-gated-transformer` | `discovery-gated-transformer-namecert` | `reports/canonical/discovery-gated-transformer.json:$.component_refs` | `reports/canonical/discovery-gated-transformer.json:$.mechanism_namecert_ref` | `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence` | `reports/canonical/discovery-gated-transformer.json:$.component_ablation` | `reports/canonical/discovery-gated-transformer.json:$.revocation_rows` | `pass`

## Not Claimed

- MechanismDNA owns only canonical mechanism vocabulary and pointer gates.
- Terminal claim decisions remain outside this artifact.
- Downstream mechanism evidence payloads remain in their source artifacts.
