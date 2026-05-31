# Automath-NewMath bridge ledger

## Design intent

This ledger defines the first bridge layer between Automath and NewMath. The
goal is not automatic content transfer. The goal is a durable protocol that lets
humans and future AI agents answer:

- Which repo, branch, commit, and path did an item come from?
- Which repo, branch, and path may consume it?
- Why is it being bridged?
- Is it only observed, or has it been accepted or consumed?
- Does it require operator review, TasteGate evidence, or another audit?
- Could it trigger paper, Lean, docs, publication, or external-send effects?

The bridge now has paired worktree branches:

- Automath: `bridge/automath-newmath-consumption`
- NewMath: `bridge/newmath-automath-consumption`

Both branches use the same manifest schema and local-only runtime directories.
The generated local manifest path is
`tools/automath_newmath_bridge/bridge_manifest.jsonl` in each repo, and it is
ignored by Git. NewMath remains an observed source through explicit refs such as
`origin/auto-dev` and `origin/codex-auto-dev`; Automath remains an observed
source through `origin/dev` and the Automath bridge worktree.

The recurring bridge supervisor is:

`tools/automath_newmath_bridge/bridge_supervisor.py`

It periodically fetches Automath and NewMath refs, merges the NewMath bridge
branch with `origin/auto-dev`, discovers new or changed artifacts, synthesizes
cross-repo readiness, runs bridge gates, optionally merges the gated bridge
branch back to `bedc-claim-packet-pipeline`, and writes local-only review
packets when explicitly enabled. Runtime outputs are ignored by Git and must
not be uploaded.

## Bridge directions

Bridge directions, source paths, destination paths, artifact mappings, and
readiness are read from the bridge configuration and runtime outputs.

- Static scan sources: `tools/automath_newmath_bridge/bridge_sources.json`
- Growth-aware source rules: `tools/automath_newmath_bridge/bridge_pipeline_config.json`
- Runtime inbox, gate output, transfer plan, and synthesis reports:
  `tools/automath_newmath_bridge/inbox/`,
  `tools/automath_newmath_bridge/out/`,
  `tools/automath_newmath_bridge/state/`, and
  `tools/automath_newmath_bridge/logs/`

Render a reviewable report from a JSONL output with:

```bash
python3 tools/automath_newmath_bridge/render_bridge_report.py <jsonl> --output <path>
```

## Accepted bridge rules

1. Every bridge item must have an explicit source repo, source ref, source path,
   source commit, destination repo, destination ref, and destination path.
2. `observed` and `candidate` records do not authorize content movement.
3. `accepted` requires operator review. A script may report candidates but may
   not mark them accepted without a human action recorded in the manifest.
4. `consumed` requires the destination path to exist or the consuming commit to
   be named in a follow-up record.
5. NewMath `\origin{ai}` chapters past seed closure require the BEDC TasteGate
   witness marker enforced by `lean4/scripts/bedc_ci.py`.
6. Automath writebacks remain governed by the distillation review gate and
   paper/Lean audits. The bridge manifest is not a writeback approval.
7. Outreach/open-problem runtime state remains separate. Bridge records may
   observe outreach patterns, but they must not write bridge state into
   `tools/community-outreach/outreach_state` or the active outreach board.
8. Public dossier or publication use has publication risk. It requires explicit
   operator approval before bridge status appears on public pages.
9. The supervisor may fetch latest refs from both repos, but it must not push.
10. Intermediate artifacts stay local-only under `inbox/`, `out/`, `state/`,
   and `logs/`.
11. Automatic writeback is limited to ignored local review packets. Durable
   paper / Lean / docs writes require accepted or consumed manifest records and
   the destination project's own gates.
12. Discovery is not readiness. The bridge must synthesize both repo contents
    before packet writes, especially for emergent NewMath constant material.
13. NewMath constant/RealConstant records are `blocked_automath_not_ready`
    until an operator chooses the receiving Automath queue and destination gate.

## Operator approval boundary

Bridge tooling may:

- scan configured source paths;
- fetch latest refs for configured repos;
- discover new or changed artifacts as both repos grow;
- read current Git refs and commits;
- generate local candidate packets;
- run deterministic bridge gates;
- write ignored local review packets after gates pass;
- validate JSONL records;
- render Markdown reports.

Bridge tooling may not:

- push to public branches;
- send email;
- post issues, comments, or social messages;
- submit papers;
- publish intermediate artifacts;
- merge `dev`, `auto-dev`, or integration branches;
- overwrite proposal or accepted proposal files;
- move source material into a durable destination without a manifest record;
- upload intermediate inbox/out/state/log artifacts to GitHub.

## TasteGate and audit boundary

NewMath BEDC has a concrete audit rule: if a chapter is marked `\origin{ai}`
and its theory closure is no longer `seedClosure`, the closure status must
reference `BEDC.Derived.<X>Up.taste_gate`. The live witness set is read from
the source tree and checked by `python3 lean4/scripts/bedc_ci.py audit`.

Automath has a different audit surface: `omega_ci.py` tracks paper claim labels,
Lean registry labels, forbidden Lean constructs, and file verification. Its
distillation tooling adds writeback review and application planning. Bridge
records must name which audit applies instead of treating both projects as one
pipeline.

## Automath evidence lookup

The bridge must reuse local Automath mechanisms where they already exist.
Use Automath's own audit and retrieval commands to find exact theorem,
paper-label, writeback, publication, and gate evidence before marking any
Automath artifact accepted or consumed. Bridge records should name exact files
and theorem labels found locally, not generic descriptions of Automath gates.

## Supervisor and gate model

The bridge supervisor follows the same operational ideas as the local
distillation, NewMath BEDC supervisor, and loning/oracle pipelines:

| Existing pattern | Bridge equivalent |
| --- | --- |
| fixed branch guard | `--branch bridge/automath-newmath-consumption` |
| stop file | `tools/automath_newmath_bridge/.bridge_supervisor.stop` |
| fetch before pass | fetch Automath and NewMath configured refs |
| auto-dev sync | merge `origin/auto-dev` into the NewMath bridge branch before scanning |
| dashboard/log file | `tools/automath_newmath_bridge/logs/bridge_supervisor.log` |
| source queue / runtime state | ignored `inbox/`, `out/`, and `state/` |
| deterministic policy gate | `bridge_gates.py` |
| cross-repo readiness synthesis | `bridge_synthesis.py` |
| merge-back after gates | optional local merge into `bedc-claim-packet-pipeline` |
| BEDC BOARD ingest | `bridge_to_bedc_board.py` calls `tools/bedc-deep/board_spawn.py` |
| review packet before writeback | ignored `inbox/writeback_packets/*.json` |
| publication / review gates | no public-facing use without explicit approval |

The bridge synthesis layer scans both repos, not just refs. The scan surface is
the configured source tree plus the discovery rules in
`tools/automath_newmath_bridge/bridge_pipeline_config.json`; the per-pass
results are written under `tools/automath_newmath_bridge/out/`.

Synthesis readiness values are intentionally conservative:

- `observe_only`: record source material only.
- `needs_operator_review`: a packet may be useful but a human must decide.
- `ready_for_local_packet`: deterministic gates may emit an ignored packet.
- `blocked_automath_not_ready`: NewMath evidence exists, but Automath has no
  selected receiving target or gate.
- `ready_for_durable_write`: reserved for future use after manifest acceptance,
  destination gate selection, and operator approval.

The bridge gate checks that a record is schema-valid, points only to safe local
review-packet destinations for automatic writes, preserves TasteGate language
when required, and blocks durable paper / Lean / docs / outreach-state writes.

Approved local packet writes are still only "needs operator review" packets.
They are not accepted or consumed manifest entries.

Automath-to-NewMath durable transfer has one allowed write path on this branch:

```text
Automath source evidence
  -> bridge discovery
  -> bridge_synthesis readiness
  -> bridge_gates
  -> ignored local bridge review packet
  -> tools/bedc-deep/board_spawn.py
  -> tools/bedc-deep/BOARD.md
  -> merge back to bedc-claim-packet-pipeline when target is clean
  -> BEDC supervisor owns paper/Lean/push
```

The bridge adapter does not write BEDC paper or Lean files. It also does not
copy a simplified BOARD writer; `board_spawn` remains the only append gate, so
fit, novelty, dedup, paper coverage, and Claude judge behavior stay native to
NewMath.

Run one supervised pass:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --once
```

Run periodically:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --poll-interval 300
```

Persist seen-state and emit local review packets:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --once \
  --update-state \
  --apply-writeback-packets
```

Apply BEDC BOARD ingest for eligible Automath-to-NewMath records:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --once \
  --apply-bedc-board-ingest
```

After gates pass, the NewMath bridge supervisor attempts to merge the gated
bridge branch back to the local BEDC branch:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --once
```

The merge-back target is configured in `bridge_pipeline_config.json` as
`../newmath` on `bedc-claim-packet-pipeline`. The merge is local-only and
skips if the target worktree is on a different branch, has uncommitted changes,
or any bridge gate is blocked.

Pass `--no-merge-back-after-gates` to run observation/gates only.

## Future AI commit analysis

Future agents should inspect commits touching this bridge by reading:

1. The commit message Source block.
2. The commit message Destination block.
3. The ignored local manifest at
   `tools/automath_newmath_bridge/bridge_manifest.jsonl`, if present.
4. Any generated packet under `tools/automath_newmath_bridge/out/`.
5. This ledger.

If a commit only changes schema, manifest, scripts, or reports, it should be
interpreted as protocol work unless a manifest line explicitly marks a bridge
item `accepted` or `consumed`.

## Commit message convention

```text
bridge(<direction>): <short action>

Source:
- repo: the-omega-institute/newmath
- ref: origin/auto-dev
- paths:
  - papers/bedc/scripts/prompts/phase_propose.txt
  - lean4/scripts/review_proposals.py
  - lean4/scripts/bedc_ci.py

Destination:
- repo: the-omega-institute/automath
- ref: bridge/automath-newmath-consumption
- paths:
  - tools/automath_newmath_bridge/...
  - docs/bridge/automath-newmath-bridge.md

Purpose:
- Establish an auditable bridge protocol before any automatic content movement.

Audit boundary:
- operator review required: yes
- TasteGate required: yes
- Lean build required: no
- external publication/send: no

AI-analysis note:
- This commit records source observation and bridge rules only. It does not
  accept, consume, publish, push, or synchronize content.
```

For Automath-to-NewMath commits, reverse the Source and Destination blocks and
keep the same audit-boundary fields.
