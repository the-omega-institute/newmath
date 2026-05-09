# Constructive-Story Field for `closurestatus`

## Motivation

Every BEDC object is bootstrapped from `BHist.Empty`, `BMark.b0`, `BMark.b1`, and recursive moves. A reader looking at a `closurestatus` block today learns *what was closed* (theory grade, formal verification, scope, upgrade path) but not *how the named concept emerges from prior layers*. Adding one short orienting field — written in our own bootstrapped vocabulary — makes each chapter self-explanatory and reinforces the project's central claim: nothing is imported, everything is laid down brick by brick.

## Decision

Add one new field, `\constructivestory`, to the `closurestatus` environment.

- Required in every block once the inject pass runs (gated by `bedc_ci.py audit`).
- Empty argument is allowed and renders nothing in the PDF; counts as a TODO that the codex pipeline picks up in subsequent rounds.
- Position: top of the block, before `\theoryclosure`.
- Single argument, English only. The Chinese version lives in the dossier glossary as a separate optional sub-field (`constructive_story_zh`) so the paper body stays Chinese-free per project convention.
- Length guidance: 1–3 sentences derived from prior chapters' macros and kernel primitives.

## Surfaces

- **Paper PDF.** Renders inline at the top of the closure block as `Constructive story: <text>` when text is non-empty.
- **Dossier detail panel.** Shown beneath the node title and above the metadata rows. EN comes from the paper; ZH comes from glossary. Active language preference picks one; falls back to EN when ZH is absent; hidden when both are empty.

## Architecture

### Paper side

`papers/bedc/preamble.tex`:

- Add a stub macro alongside the other field-name tokens (used outside the environment as a math display name, mirroring `\scopeclosed` etc.):

  ```latex
  \newcommand{\constructivestory}{\mathsf{constructivestory}}
  ```

- Inside the `closurestatus` environment, add a real definition that swallows empty arguments silently:

  ```latex
  \def\constructivestory##1{%
    \ifx\\##1\\\else\par\textbf{Constructive story:} ##1\par\fi%
  }%
  ```

  Place this `\def` first inside the environment body so the rendered row appears at the top of each block.

### Inject pass

`tools/inject_constructive_story.py` (new script, stdlib-only, idempotent):

- Walks `papers/bedc/parts/`.
- For each `\begin{closurestatus}{...}` line, looks ahead within the same block (until `\end{closurestatus}`) for an existing `\constructivestory` line.
- If absent, inserts `  \constructivestory{}` on the line immediately after `\begin{closurestatus}{...}`, preserving indentation style.
- Re-running it is a no-op on already-injected files.
- Reports how many files were modified vs already had the field.

### CI gate

`lean4/scripts/bedc_ci.py audit`:

- After the existing scans, walk every chapter that contains `\begin{closurestatus}`.
- Fail if a block lacks a `\constructivestory{...}` line (empty arg counts as present).
- Error message names the file and the block's `\NameCert_{...}` token.

### Dossier extraction

`tools/build_dossier_status.py`:

- Extend the closure-block scanner (`collect_closure_per_region`) to capture the `\constructivestory{...}` argument.
- Per-region: store `constructive_story_en` (string, possibly empty).
- `build_glossary()` already loads `data_source/glossary.json`; pass through any `constructive_story_zh` field on each entry.
- In `build_dependency_graph()`, attach both fields to each node: `constructive_story_en`, `constructive_story_zh` (either may be empty/absent).

### Glossary source

`docs/dossier/data_source/glossary.json`:

- Schema extension on each entry (optional):

  ```json
  "nat": {
    "en": { "label": "Nat", "desc": "..." },
    "zh": { "label": "自然数", "desc": "..." },
    "constructive_story_zh": "...",
    "aliases": [...]
  }
  ```

- Initially empty across the board. Codex fills regions as the corresponding paper text matures.
- `tools/check_glossary.py` is unchanged for now; we may add an advisory pass later that reports en-present-but-zh-absent regions.

### Visualization

`docs/dossier/visualization.qmd` detail panel:

- Insert a story block right after the node title (`<h3>` line) and before the metadata rows.
- Renders: `<p class="constructive-story">${story}</p>` when story is non-empty.
- `story = (LANG === "zh" ? node.constructive_story_zh : null) || node.constructive_story_en || null`.
- Style: light italic with a left rule, distinguishable from regular paragraphs but visually quiet.
- No heading prefix — the node title above already provides context, and the field renders as a single styled paragraph.

## Backfill plan

- The inject script touches all 183 chapters in one commit, adding empty `\constructivestory{}` placeholders where missing.
- No manual content backfill in this round.
- Codex pipeline (`papers/bedc/scripts/codex_revise.py`) naturally picks up empty placeholders and fills them in subsequent R-rounds.
- Glossary `constructive_story_zh` entries: codex fills incrementally as it writes content for each region.

## Atomic commit

Per CLAUDE.md discipline, this lands as a single commit:

1. Preamble macro (rendering rule)
2. CI gate (`bedc_ci.py audit` extension)
3. Inject script (`tools/inject_constructive_story.py`)
4. Result of running the inject script (183 chapters with empty placeholders)
5. Dossier extractor (`tools/build_dossier_status.py`)
6. Visualization renderer (`docs/dossier/visualization.qmd`)

Splitting any of these creates an intermediate state where CI is broken (rule landed but chapters unupdated) or the rule is silent (chapters changed but no rendering or gate). Single atomic commit avoids that.

The glossary file (`docs/dossier/data_source/glossary.json`) needs no change in this commit: `constructive_story_zh` is an optional sub-field on existing entries; consumers handle its absence as "no Chinese yet." Codex commits will add that data later, region by region.

## Out of scope

- Translating the existing `scopeclosed` / `notclaimed` / `upgradepath` fields into Chinese. Only the new field surfaces bilingually.
- Auto-generating English content from Lean dependency chains. Authorial / codex-written prose only.
- Enforcement of "uses only prior layers" — this is authorial discipline, not a checked invariant.
- Backfilling glossary `constructive_story_zh` for any region in this round.

## Risks

- The atomic commit modifies ~185 files (preamble + inject script + 183 chapters + extractor + viz). Per CLAUDE.md, this is an unusually large bundle and risks colliding with parallel codex workers. Mitigation: pick a quiet `gh run list --branch codex-auto-dev` window before pushing; rely on the per-worker rebase fix already in place.
- Codex content quality is uneven; some early-filled stories may need human revision. Acceptable: better to have placeholders inviting fill than no field at all.
