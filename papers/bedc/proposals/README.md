# BEDC AI-Proposed Chapter Proposals

This directory holds chapter proposals written by codex (or any other AI
caller) before they enter the BEDC horizon as full seed-stub chapters.
Each file is a single proposal whose acceptance is decided by an
operator review step.

## Proposal lifecycle

```
codex Phase Propose         papers/bedc/proposals/<sha>_<slug>.md
  ─── proposal written
                       │
                       ▼
operator review (review_proposals.py)
  ─── accept ──────►   seed-stub chapter
                       (papers/bedc/parts/concrete_instances/
                        <NN>_<slug>_namecert_construction.tex)
                       with \origin{ai} on its closurestatus block
                       │
                       ▼
                       audit gate enforces TasteGate instance
                       before chapter can leave seedClosure
                       │
                       ▼
                       AI chapter joins the horizon via the same
                       paper / lean rounds as human-curated chapters
                       │
  ─── reject ──────►   archived in proposals/rejected/<sha>_<slug>.md
                       with operator's rejection reason; future
                       phase_propose prompts learn from rejected
                       cases
```

## Proposal file format

Each proposal is a single markdown file at `proposals/<sha>_<slug>.md`
where:

- `<sha>` is the short git commit SHA at the time of proposal (8 chars)
- `<slug>` is a kebab-case identifier matching the proposed chapter,
  e.g. `belief-up`, `policy-up`, `worldmodel-up`

Required sections (in order):

```markdown
# <X>Up

## Carrier sketch

One paragraph describing what `\<X>Up` is at the BHist level. Must
mention which finite history rows describe the object and how the
classifier hsame controls equivalence. Must cite at least 3 existing
BEDC chapters as dependency anchors (e.g. "depends on
\NameCert{NatUp}, \NameCert{SeqUp}, \NameCert{ComputableUp}").

## TasteGate sketch

Four short paragraphs, one per obligation:

1. **Conservativity**: which baseline-only formulas are unaffected
   by introducing `\<X>Up`, and the proof outline.
2. **No hidden input**: how every `\<X>Up`-token reduces to a finite
   event-flow recognition (cite ground_compiler chapter if useful).
3. **Round trip**: which display readback is invertible, and the
   proof outline (typically by induction on the constructor history).
4. **Layer separation**: how the chapter's source / channel / display
   roles stay disjoint.

## Five NameCert obligations sketch

One paragraph each for source / classifier / pattern / ledger /
extension, in BEDC vocabulary (BHist, hsame, Cont, Pkg).

## Why this is a real theory, not combinatorial padding

One paragraph defending why the chapter introduces a new mathematical
object rather than a renaming of an existing chapter or a trivial
construction. Must reference at least one published mathematical
result, AI alignment paper, or formalization community discussion
that motivates the chapter.

## Cannot-claim

One paragraph listing what the chapter does NOT close (analogous to
the human-curated chapters' \notclaimed field).
```

## Review CLI

```
python3 lean4/scripts/review_proposals.py list
  -- list pending proposals with summary header

python3 lean4/scripts/review_proposals.py show <sha>
  -- pretty-print a proposal

python3 lean4/scripts/review_proposals.py accept <sha>
  -- promote to seed-stub chapter:
       creates papers/bedc/parts/concrete_instances/<NN>_<slug>_namecert_construction.tex
       with \origin{ai} on closurestatus
       adds \input line to main.tex
       adds preamble macro
       moves proposal to proposals/accepted/

python3 lean4/scripts/review_proposals.py reject <sha> --reason "..."
  -- archive to proposals/rejected/<sha>_<slug>.md
       (rejection reason embedded; phase_propose can ingest)
```

## Acceptance criteria (operator judgement)

A proposal should be accepted when ALL of:

- TasteGate sketch's four obligations are plausible (operator believes
  a Lean instance can be supplied within ~1-3 days of pipeline work).
- NameCert sketch is in BEDC vocabulary, no smuggled mathlib concepts.
- Carrier sketch cites concrete dependency chapters (not generic).
- "Why this is a real theory" paragraph is convincing (not handwave).
- Slug doesn't collide (case-insensitive) with any existing chapter
  in `papers/bedc/parts/concrete_instances/`.

When rejecting, briefly state which criterion fails. Rejected
proposals stay archived for `phase_propose` prompt feedback.

## Phase 2 status: scaffolding only

As of the initial Phase 2 setup, this directory exists but the
phase_propose codex trigger is NOT wired into `codex_revise.py`.
Proposals are accepted only via operator hand-write or via codex
running phase_propose on demand. The auto-trigger conditions
(`closed/open > 2`, propose-cooldown) will be added once Phase 1
audit gate is observed running cleanly for 1-2 weeks.
