# Discovery Level Semantics

Discovery levels are current output labels owned by `reports/canonical/discovery_map.json`.

`D5-O` means robust operational discovery: a positive discovery has passed the robustness gates used by the canonical gap-head evidence chain, including acceptance gates and final report status. It does not claim mechanism attribution closure.

`D5-M` means mechanism-closed discovery: the `D5-O` operational gate is satisfied and mechanism attribution hardgates all pass. A blocked or failed attribution gate blocks `D5-M`.

`probe-margin-channel` is a mechanism evidence status, not a mechanism closure channel. Any `probe-margin-channel` mechanism status blocks `D5-M` and leaves the positive robust claim at `D5-O`.
