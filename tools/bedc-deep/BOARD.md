# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-578 - Two-$\SubgroupUp$ intersection is a $\SubgroupUp$ certificate (abstract version)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Two-$\SubgroupUp$ intersection is a $\SubgroupUp$ certificate (abstract version) |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For a fixed $\GroupUp$ source and any two $\SubgroupUp$ predicates $H_1, H_2$ on its carrier, the carrier $H_{1,2}(x) :\Leftrightarrow H_1(x) \land H_2(x)$ with restricted $\hsame$ classifier satisfies the $\SubgroupUp$ certificate rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/58_subgroup_namecert_construction_core.tex`
- `papers/bedc/parts/concrete_instances/subgroup/`

Rationale:
Concrete instances chapter (subgroup). Textbook-standard: 'the intersection of two subgroups is a subgroup' (Hungerford Algebra ch.I §2 Thm.2.5; Dummit & Foote ch.2). BEDC currently has only specialised intersections — `\thm:subgroup-centralizer-intersection-certificate` (58_subgroup_namecert_construction_core.tex:86) for two centralizers. The general two-subgroup version is a direct generalisation: the proof of the centralizer-intersection theorem (lines 107-145) componentwise unpacks two centralizer witnesses; the same shape works for arbitrary SubgroupUp predicates by using `\thm:subgroup-one-step-criterion` (subgroup chain) instead of centralizer-specific rows. Closes in 1-3 rounds: identity row pair, product closure pair, inverse closure pair, hsame transport pair. Land in new child `subgroup/abstract_two_subgroup_intersection.tex` (core file at 745 lines is borderline). NOT covered by B-466 (matroid intersection right subset projection) or any centralizer-intersection BOARD entry.

---

