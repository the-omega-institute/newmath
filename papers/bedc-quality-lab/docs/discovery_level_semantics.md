# Discovery Level Semantics

Discovery levels are current output labels owned by `reports/canonical/discovery_map.json`.

`D5-O` means robust operational discovery: a positive discovery has passed the robustness gates used by the canonical gap-head evidence chain, including acceptance gates and final report status. It does not claim mechanism attribution closure.

`D5-M` means mechanism-closed discovery: the `D5-O` operational gate is satisfied, `$.mechanism_evidence.evidence_level` is a resolved causal evidence level in `patch | intervention | counterfactual`, mechanism attribution hardgates all pass, and observational-only or ablation-only evidence is never sufficient.

`probe-margin-channel` is a mechanism evidence status, not a mechanism closure channel. Any `probe-margin-channel` mechanism status blocks `D5-M` and leaves the positive robust claim at `D5-O`.
