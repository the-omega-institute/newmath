---
name: write-dossier
description: Use when writing or updating BEDC dossier essays under docs/dossier, especially bilingual Chinese/English philosophy articles that end with strict mathematical formalization.
---

# Write Dossier

## Goal

Create or update `docs/dossier` essays in the project dossier style: bilingual
paired articles, metaphor-rich philosophical prose first, strict mathematical
schema last, and full site integration.

## Scope

- Work in `docs/dossier`.
- Create paired files:
  - English: `<slug>.qmd`
  - Chinese: `<slug>.zh-CN.qmd`
- Update both `docs/dossier/index.qmd` and `docs/dossier/index.zh-CN.qmd`.
- Update `docs/dossier/_quarto.yml` navigation when the article should be
  directly discoverable from the navbar.

## Style

- Use dossier voice, not paper theorem voice: natural philosophy, concrete
  analogies, and readable sections.
- Use many metaphors when the user asks for philosophical articles: room,
  window, map, riverbed, loom, ledger, harbor, prism, clock city, stage, key,
  shadow, or other domain-fitting images.
- End with `## Strict Mathematical Form` in English and `## 严格数学形式` in
  Chinese.
- The final section must be mathematically disciplined: define carriers,
  ledgers, equivalence relations, forcing judgments, gauge/representation
  quotients, and cannot-claim boundaries where relevant.
- Do not overclaim. For GR/QM/physics, write relative forcing claims of the
  form
  `BEDC + observation ledger + admissible candidate class + audited probes =>
  gauge/representation class`, not unconditional derivation from the empty
  kernel.
- Preserve paired language links:
  - English file links to `.zh-CN.qmd`
  - Chinese file links to English `.qmd`
- Use the existing CTA pattern at the end when nearby dossier pages exist.

## Front Matter Pattern

English:

```yaml
---
title: "<Title>"
subtitle: "<Specific one-line thesis>"
author: "The Omega Institute"
date: YYYY-MM-DD
description: "A bilingual dossier essay on ..."
---
```

Chinese:

```yaml
---
title: "<中文标题>"
subtitle: "<中文副标题>"
author: "The Omega Institute"
date: YYYY-MM-DD
lang: zh-Hans
description: "一篇中文 dossier: ..."
---
```

Use the actual current date only for newly authored dossier pages. Do not
change dates on existing pages unless the user explicitly asks.

## Workflow

1. Read nearby examples before writing:
   - `docs/dossier/projection-geometry-and-the-closed-world.qmd`
   - `docs/dossier/projection-geometry-and-the-closed-world.zh-CN.qmd`
   - `docs/dossier/interface-constraint-section.qmd`
   - `docs/dossier/interface-constraint-section.zh-CN.qmd`
2. Choose a semantic lowercase slug, no version/round labels.
3. Draft the English and Chinese files as parallel essays, not literal
   line-by-line translations.
4. Add both files to the matching `listing.contents` block in
   `index.qmd` / `index.zh-CN.qmd`.
5. If suitable, add the English page to `_quarto.yml` under the relevant
   navbar section. The site navbar currently uses English links; the page
   itself provides the Chinese switch.
6. Compare all `.qmd` files against the two listing blocks and add any real
   dossier essay that is missing. Exclude tool/project pages such as
   `index*.qmd`, `paper.qmd`, `visualization.qmd`, `rule110-visualization.qmd`,
   `taste-evolutions.qmd`, `discovery-quality-sieve*.qmd`, and
   `structural-discovery-dna*.qmd`.

## Checks

Run:

```bash
PYTHONPATH=. python3 tools/test_dossier_runtime.py
git diff --check
```

For Quarto rendering, prefer rendering the touched pages:

```bash
quarto render docs/dossier/<slug>.qmd
quarto render docs/dossier/<slug>.zh-CN.qmd
```

If using `quarto preview` from a Codex worktree under `.codex/worktrees`, be
aware that Quarto may discover zero project inputs because the path is under a
hidden directory. Work around this by syncing the dossier folder to a
non-hidden temporary directory and running preview there:

```bash
rsync -a --delete --exclude='.quarto/' --exclude='_site/' docs/dossier/ /Users/auric/newmath-dossier-preview/
cd /Users/auric/newmath-dossier-preview
quarto preview . --host 127.0.0.1 --port 4321 --no-browser
```

After index/listing edits, clear preview cache before restarting if the
listing does not refresh:

```bash
rm -rf /Users/auric/newmath-dossier-preview/_site /Users/auric/newmath-dossier-preview/.quarto
```

## Common Mistakes

- Adding a page to `_quarto.yml` but not to both listing blocks.
- Trusting Quarto cached preview after listing edits; restart preview if
  the Recent updates list looks stale.
- Writing a metaphor-only article with no final formal schema.
- Claiming GR/QM follows directly from BEDC without ledger, candidate, probe,
  gauge, and gap parameters.
- Creating English-only or Chinese-only pages unless the user explicitly asks.
