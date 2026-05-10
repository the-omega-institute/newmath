# Capstones → NameCert Unified Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Physically merge `papers/bedc/parts/capstones/` into `papers/bedc/parts/concrete_instances/` and rewrite each migrated chapter as a NameCert 5-tuple with closurestatus block, achieving full schema uniformity (every BEDC paper chapter is one NameCert).

**Architecture:** Two phases in single branch `capstones-physical-migration`:
- **Phase 1** — Atomic physical migration (1 commit): file moves + path/label/namespace sed + main.tex update. Content stays as散文 narratives; only locations and references change.
- **Phase 2** — Per-chapter NameCert rewrite (25 commits, one per migrated chapter): rewrite散文 as Source/Pattern/Classifier/Stability/Ledger 5-tuple, add `closurestatus` block, update Lean target if needed, run all 5 gates.

**Tech Stack:**
- LaTeX (`papers/bedc/`), `pdflatex` double-pass via `make`
- Lean 4 (`lean4/`), `lake build`, mathlib-free
- Python audit scripts: `tools/check-axioms.py`, `lean4/scripts/bedc_ci.py {audit, axiom-purity --strict}`
- `codex exec` CLI for per-chapter mechanical rewrites
- `git` (atomic commits, merge-not-rebase per CLAUDE.md)
- `gh` CLI for PR creation/merge

---

## Phase 0: Branch + Pre-flight

### Task 0.1: Confirm branch and clean state

**Files:** None (read-only checks)

- [ ] **Step 1: Verify on target branch with clean tree**

```bash
cd /Users/auric/newmath
git rev-parse --abbrev-ref HEAD
git status --short
```

Expected: `capstones-physical-migration` and empty status.

- [ ] **Step 2: Verify base is at recent auto-dev**

```bash
git fetch origin auto-dev
git log --oneline origin/auto-dev..HEAD | wc -l
git log --oneline HEAD..origin/auto-dev | wc -l
```

Expected: 0 ahead of base, possibly some behind (from parallel codex-auto-dev pipeline). If behind, merge.

- [ ] **Step 3: If behind origin/auto-dev, merge it in**

```bash
git merge origin/auto-dev --no-edit
```

If conflicts, resolve manually (capstones content unlikely to conflict).

- [ ] **Step 4: Verify all 5 gates pass on clean baseline**

```bash
cd lean4 && lake build && cd ..
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity --strict
cd papers/bedc && make check && cd ../..
```

Expected: all exit 0. If any fails, STOP — don't start migration on broken baseline.

### Task 0.2: Audit and lock the migration table

**Files:** Create `/tmp/capstones_migration_table.csv` (scratch, not committed)

- [ ] **Step 1: Generate file list + chosen NameCert object names**

```bash
ls papers/bedc/parts/capstones/*.tex 2>/dev/null > /tmp/cap_top.txt
ls papers/bedc/parts/capstones/*/*.tex 2>/dev/null > /tmp/cap_sub.txt
wc -l /tmp/cap_top.txt /tmp/cap_sub.txt
```

Expected: 16 top-level files (15 capstones + 1 index.tex), ~7 subdir files.

- [ ] **Step 2: Write `/tmp/capstones_migration_table.csv`**

Format: `old_path,new_path,namecert_object_name,object_kind`

```csv
old_path,new_path,namecert_object,kind
papers/bedc/parts/capstones/compact_uniform_continuity.tex,papers/bedc/parts/concrete_instances/270_compact_uniform_continuity_namecert_construction.tex,CompactUniformContinuityUp,bridge
papers/bedc/parts/capstones/compilation_as_namecert_morphism.tex,papers/bedc/parts/concrete_instances/271_compilation_morphism_namecert_construction.tex,CompilationMorphismUp,morphism
papers/bedc/parts/capstones/computation_as_continuation.tex,papers/bedc/parts/concrete_instances/272_computation_continuation_namecert_construction.tex,ComputationContinuationUp,morphism
papers/bedc/parts/capstones/empty_fable_machine.tex,papers/bedc/parts/concrete_instances/273_empty_fable_machine_namecert_construction.tex,EmptyFableMachineUp,object
papers/bedc/parts/capstones/halting_as_form_of_distinction_limit.tex,papers/bedc/parts/concrete_instances/274_halting_distinction_limit_namecert_construction.tex,HaltingDistinctionLimitUp,bridge
papers/bedc/parts/capstones/inter_hist_locality.tex,papers/bedc/parts/concrete_instances/275_inter_hist_locality_namecert_construction.tex,InterHistLocalityUp,bridge
papers/bedc/parts/capstones/kernel_as_category.tex,papers/bedc/parts/concrete_instances/276_kernel_category_namecert_construction.tex,KernelCategoryUp,morphism
papers/bedc/parts/capstones/observer_hist_identity.tex,papers/bedc/parts/concrete_instances/277_observer_hist_identity_namecert_construction.tex,ObserverHistIdentityUp,bridge
papers/bedc/parts/capstones/real_completeness.tex,papers/bedc/parts/concrete_instances/278_real_completeness_namecert_construction.tex,RealCompletenessUp,bridge
papers/bedc/parts/capstones/reasoning_by_contradiction_boundary.tex,papers/bedc/parts/concrete_instances/279_reasoning_contradiction_boundary_namecert_construction.tex,ReasoningContradictionBoundaryUp,meta
papers/bedc/parts/capstones/reflection_and_limits.tex,papers/bedc/parts/concrete_instances/280_reflection_limits_namecert_construction.tex,ReflectionLimitsUp,meta
papers/bedc/parts/capstones/riemann_hypothesis.tex,papers/bedc/parts/concrete_instances/281_riemann_hypothesis_namecert_construction.tex,RiemannHypothesisUp,bridge
papers/bedc/parts/capstones/theory_stability_taste_gate.tex,papers/bedc/parts/concrete_instances/282_taste_gate_namecert_construction.tex,TasteGateUp,meta
papers/bedc/parts/capstones/three_axioms_one_closure.tex,papers/bedc/parts/concrete_instances/283_three_axioms_closure_namecert_construction.tex,MetaClosureMoveUp,meta
papers/bedc/parts/capstones/type_checking_as_classifier_membership.tex,papers/bedc/parts/concrete_instances/284_type_checking_classifier_namecert_construction.tex,TypeCheckingClassifierUp,bridge
papers/bedc/parts/capstones/axiszeckendorf/unary_direction_bridge.tex,papers/bedc/parts/concrete_instances/axiszeckendorf/unary_direction_bridge.tex,UnaryDirectionBridgeUp,bridge
papers/bedc/parts/capstones/axiszeckendorf/zeckendorf_carry_classifier.tex,papers/bedc/parts/concrete_instances/axiszeckendorf/zeckendorf_carry_classifier.tex,ZeckendorfCarryClassifierUp,bridge
papers/bedc/parts/capstones/axiszeckendorf/axis_zeckendorf_cannot_claim.tex,papers/bedc/parts/concrete_instances/axiszeckendorf/axis_zeckendorf_cannot_claim.tex,AxisZeckendorfCannotClaimUp,meta
papers/bedc/parts/capstones/real_completeness/transported_stationary_diagonal.tex,papers/bedc/parts/concrete_instances/real_completeness/transported_stationary_diagonal.tex,TransportedStationaryDiagonalUp,bridge
papers/bedc/parts/capstones/rh/contour_integral_operation.tex,papers/bedc/parts/concrete_instances/rh/contour_integral_operation.tex,ContourIntegralOperationUp,bridge
papers/bedc/parts/capstones/rh/analytic_continuation_operation.tex,papers/bedc/parts/concrete_instances/rh/analytic_continuation_operation.tex,AnalyticContinuationOperationUp,bridge
papers/bedc/parts/capstones/rh/zeta_continuation_application.tex,papers/bedc/parts/concrete_instances/rh/zeta_continuation_application.tex,ZetaContinuationApplicationUp,bridge
```

This is the canonical mapping. Lock it before Phase 1. Total: 22 chapters (15 top + 7 subdir).

- [ ] **Step 3: Verify no name collisions in concrete_instances**

```bash
for n in 270 271 272 273 274 275 276 277 278 279 280 281 282 283 284; do
  ls papers/bedc/parts/concrete_instances/${n}_*.tex 2>/dev/null
done
ls -d papers/bedc/parts/concrete_instances/{axiszeckendorf,real_completeness,rh} 2>&1 | grep -v "No such"
```

Expected: no output (numbers free, subdirs free).

---

## Phase 1: Physical Migration (single atomic commit)

### Task 1.1: Move top-level capstone files with rename

**Files:**
- Move: 15 files via `git mv` (per migration table)

- [ ] **Step 1: Execute git mv for 15 top-level files**

```bash
cd /Users/auric/newmath
git mv papers/bedc/parts/capstones/compact_uniform_continuity.tex             papers/bedc/parts/concrete_instances/270_compact_uniform_continuity_namecert_construction.tex
git mv papers/bedc/parts/capstones/compilation_as_namecert_morphism.tex       papers/bedc/parts/concrete_instances/271_compilation_morphism_namecert_construction.tex
git mv papers/bedc/parts/capstones/computation_as_continuation.tex            papers/bedc/parts/concrete_instances/272_computation_continuation_namecert_construction.tex
git mv papers/bedc/parts/capstones/empty_fable_machine.tex                    papers/bedc/parts/concrete_instances/273_empty_fable_machine_namecert_construction.tex
git mv papers/bedc/parts/capstones/halting_as_form_of_distinction_limit.tex   papers/bedc/parts/concrete_instances/274_halting_distinction_limit_namecert_construction.tex
git mv papers/bedc/parts/capstones/inter_hist_locality.tex                    papers/bedc/parts/concrete_instances/275_inter_hist_locality_namecert_construction.tex
git mv papers/bedc/parts/capstones/kernel_as_category.tex                     papers/bedc/parts/concrete_instances/276_kernel_category_namecert_construction.tex
git mv papers/bedc/parts/capstones/observer_hist_identity.tex                 papers/bedc/parts/concrete_instances/277_observer_hist_identity_namecert_construction.tex
git mv papers/bedc/parts/capstones/real_completeness.tex                      papers/bedc/parts/concrete_instances/278_real_completeness_namecert_construction.tex
git mv papers/bedc/parts/capstones/reasoning_by_contradiction_boundary.tex    papers/bedc/parts/concrete_instances/279_reasoning_contradiction_boundary_namecert_construction.tex
git mv papers/bedc/parts/capstones/reflection_and_limits.tex                  papers/bedc/parts/concrete_instances/280_reflection_limits_namecert_construction.tex
git mv papers/bedc/parts/capstones/riemann_hypothesis.tex                     papers/bedc/parts/concrete_instances/281_riemann_hypothesis_namecert_construction.tex
git mv papers/bedc/parts/capstones/theory_stability_taste_gate.tex            papers/bedc/parts/concrete_instances/282_taste_gate_namecert_construction.tex
git mv papers/bedc/parts/capstones/three_axioms_one_closure.tex               papers/bedc/parts/concrete_instances/283_three_axioms_closure_namecert_construction.tex
git mv papers/bedc/parts/capstones/type_checking_as_classifier_membership.tex papers/bedc/parts/concrete_instances/284_type_checking_classifier_namecert_construction.tex
```

- [ ] **Step 2: Verify mv result**

```bash
ls papers/bedc/parts/concrete_instances/2{7,8}*_namecert_construction.tex | wc -l
```

Expected: 15.

### Task 1.2: Move subdirectory files

**Files:**
- Move: 7 files in 3 subdirs via `git mv`

- [ ] **Step 1: Create destination subdirs and move files**

```bash
mkdir -p papers/bedc/parts/concrete_instances/axiszeckendorf
mkdir -p papers/bedc/parts/concrete_instances/real_completeness
mkdir -p papers/bedc/parts/concrete_instances/rh

git mv papers/bedc/parts/capstones/axiszeckendorf/unary_direction_bridge.tex     papers/bedc/parts/concrete_instances/axiszeckendorf/unary_direction_bridge.tex
git mv papers/bedc/parts/capstones/axiszeckendorf/zeckendorf_carry_classifier.tex papers/bedc/parts/concrete_instances/axiszeckendorf/zeckendorf_carry_classifier.tex
git mv papers/bedc/parts/capstones/axiszeckendorf/axis_zeckendorf_cannot_claim.tex papers/bedc/parts/concrete_instances/axiszeckendorf/axis_zeckendorf_cannot_claim.tex

git mv papers/bedc/parts/capstones/real_completeness/transported_stationary_diagonal.tex papers/bedc/parts/concrete_instances/real_completeness/transported_stationary_diagonal.tex

git mv papers/bedc/parts/capstones/rh/contour_integral_operation.tex      papers/bedc/parts/concrete_instances/rh/contour_integral_operation.tex
git mv papers/bedc/parts/capstones/rh/analytic_continuation_operation.tex papers/bedc/parts/concrete_instances/rh/analytic_continuation_operation.tex
git mv papers/bedc/parts/capstones/rh/zeta_continuation_application.tex   papers/bedc/parts/concrete_instances/rh/zeta_continuation_application.tex
```

- [ ] **Step 2: Verify moves**

```bash
ls papers/bedc/parts/concrete_instances/{axiszeckendorf,real_completeness,rh}/*.tex
```

Expected: 7 files listed.

### Task 1.3: Move Lean modules

**Files:**
- Move: `lean4/BEDC/Capstone/EmptyFableMachine.lean` → `lean4/BEDC/Derived/EmptyFableMachine.lean`
- Inspect/merge: `lean4/BEDC/Capstone.lean` → potentially merge into `lean4/BEDC.lean` umbrella

- [ ] **Step 1: Inspect Capstone.lean content**

```bash
cat lean4/BEDC/Capstone.lean
```

It's likely a small umbrella file (`import BEDC.Capstone.EmptyFableMachine`). Note its content for next step.

- [ ] **Step 2: Move EmptyFableMachine.lean and delete Capstone.lean**

```bash
git mv lean4/BEDC/Capstone/EmptyFableMachine.lean lean4/BEDC/Derived/EmptyFableMachine.lean
git rm lean4/BEDC/Capstone.lean
rmdir lean4/BEDC/Capstone 2>/dev/null || true
```

- [ ] **Step 3: Update lean4/BEDC.lean umbrella**

Find the line(s) referencing `BEDC.Capstone*` and replace with `BEDC.Derived.EmptyFableMachine`:

```bash
grep -n "Capstone" lean4/BEDC.lean
```

Then with sed:

```bash
sed -i '' 's|import BEDC\.Capstone\.EmptyFableMachine|import BEDC.Derived.EmptyFableMachine|g' lean4/BEDC.lean
sed -i '' '/^import BEDC\.Capstone$/d' lean4/BEDC.lean
```

- [ ] **Step 4: Update the moved Lean file's namespace declaration**

```bash
sed -i '' 's|namespace BEDC\.Capstone|namespace BEDC.Derived|g' lean4/BEDC/Derived/EmptyFableMachine.lean
sed -i '' 's|^namespace Capstone|namespace Derived|g' lean4/BEDC/Derived/EmptyFableMachine.lean
```

- [ ] **Step 5: Smoke test Lean still parses**

```bash
cd lean4 && lake build BEDC.Derived.EmptyFableMachine 2>&1 | tail -5 && cd ..
```

If errors, manually fix the namespace in the file. Expected: builds cleanly.

### Task 1.4: Sed cross-references throughout repo

**Files:**
- Modify: all `papers/bedc/parts/**/*.tex` and `lean4/**/*.lean` containing capstone refs

- [ ] **Step 1: Sed paper autoref + label (8 prefixes × 2 = 16 patterns)**

```bash
cd /Users/auric/newmath
for prefix in ch sec thm def prin cor prop lemma; do
  find papers/bedc/parts -name "*.tex" -print0 | xargs -0 sed -i '' \
    -e "s|\\\\autoref{${prefix}:capstones-|\\\\autoref{${prefix}:concrete-instances-|g" \
    -e "s|\\\\label{${prefix}:capstones-|\\\\label{${prefix}:concrete-instances-|g"
done
```

- [ ] **Step 2: Verify no `capstones-` label/autoref remains**

```bash
grep -rE '\\\\(autoref|label)\{[a-z]+:capstones-' papers/bedc/parts/ 2>/dev/null | head -5
```

Expected: empty (no matches). If matches, investigate (might be in commented-out code or unusual prefix).

- [ ] **Step 3: Sed paper-side Lean namespace markers**

```bash
find papers/bedc/parts -name "*.tex" -print0 | xargs -0 sed -i '' \
  -e 's|BEDC\.Capstone\.|BEDC.Derived.|g' \
  -e 's|BEDC\.Capstone\\_|BEDC.Derived\\_|g'
```

- [ ] **Step 4: Verify no `BEDC.Capstone` markers remain**

```bash
grep -rE 'BEDC\.Capstone' papers/bedc/parts/ 2>/dev/null | head -5
```

Expected: empty.

- [ ] **Step 5: Sed Lean source namespace + import (already partially done in Task 1.3, this catches any remaining)**

```bash
find lean4/BEDC -name "*.lean" -print0 | xargs -0 sed -i '' \
  -e 's|BEDC\.Capstone\b|BEDC.Derived|g'
```

- [ ] **Step 6: Verify no Lean refs remain**

```bash
grep -rE 'BEDC\.Capstone' lean4/ 2>/dev/null | head -5
```

Expected: empty.

### Task 1.5: Update \input paths throughout

**Files:**
- Modify: `papers/bedc/main.tex`
- Modify: any `papers/bedc/parts/**/*.tex` that `\input{parts/capstones/...}`

- [ ] **Step 1: Generate the \input path mapping**

Top-level mappings need explicit entries because filenames changed:

```bash
cat > /tmp/input_remap.sed <<'EOF'
s|\\input{parts/capstones/compact_uniform_continuity}|\\input{parts/concrete_instances/270_compact_uniform_continuity_namecert_construction}|g
s|\\input{parts/capstones/compilation_as_namecert_morphism}|\\input{parts/concrete_instances/271_compilation_morphism_namecert_construction}|g
s|\\input{parts/capstones/computation_as_continuation}|\\input{parts/concrete_instances/272_computation_continuation_namecert_construction}|g
s|\\input{parts/capstones/empty_fable_machine}|\\input{parts/concrete_instances/273_empty_fable_machine_namecert_construction}|g
s|\\input{parts/capstones/halting_as_form_of_distinction_limit}|\\input{parts/concrete_instances/274_halting_distinction_limit_namecert_construction}|g
s|\\input{parts/capstones/inter_hist_locality}|\\input{parts/concrete_instances/275_inter_hist_locality_namecert_construction}|g
s|\\input{parts/capstones/kernel_as_category}|\\input{parts/concrete_instances/276_kernel_category_namecert_construction}|g
s|\\input{parts/capstones/observer_hist_identity}|\\input{parts/concrete_instances/277_observer_hist_identity_namecert_construction}|g
s|\\input{parts/capstones/real_completeness}|\\input{parts/concrete_instances/278_real_completeness_namecert_construction}|g
s|\\input{parts/capstones/reasoning_by_contradiction_boundary}|\\input{parts/concrete_instances/279_reasoning_contradiction_boundary_namecert_construction}|g
s|\\input{parts/capstones/reflection_and_limits}|\\input{parts/concrete_instances/280_reflection_limits_namecert_construction}|g
s|\\input{parts/capstones/riemann_hypothesis}|\\input{parts/concrete_instances/281_riemann_hypothesis_namecert_construction}|g
s|\\input{parts/capstones/theory_stability_taste_gate}|\\input{parts/concrete_instances/282_taste_gate_namecert_construction}|g
s|\\input{parts/capstones/three_axioms_one_closure}|\\input{parts/concrete_instances/283_three_axioms_closure_namecert_construction}|g
s|\\input{parts/capstones/type_checking_as_classifier_membership}|\\input{parts/concrete_instances/284_type_checking_classifier_namecert_construction}|g
s|\\input{parts/capstones/axiszeckendorf/|\\input{parts/concrete_instances/axiszeckendorf/|g
s|\\input{parts/capstones/real_completeness/|\\input{parts/concrete_instances/real_completeness/|g
s|\\input{parts/capstones/rh/|\\input{parts/concrete_instances/rh/|g
EOF
```

- [ ] **Step 2: Apply remap to all .tex files**

```bash
find papers/bedc -name "*.tex" -print0 | xargs -0 sed -i '' -f /tmp/input_remap.sed
```

- [ ] **Step 3: Verify no `parts/capstones/` paths remain in any \input**

```bash
grep -rn '\\input{parts/capstones' papers/bedc/ 2>/dev/null | head -5
```

Expected: empty. (`capstones/index` and `capstones/_index_files` may still match if main.tex/_index_files reference them; they will be handled by Task 1.6.)

### Task 1.6: Update main.tex (remove Capstones part, add concrete_instances entries)

**Files:**
- Modify: `papers/bedc/main.tex` lines 286-302 (remove `\part{Capstones}` block, add new `\input` lines)

- [ ] **Step 1: Inspect main.tex around the changes**

```bash
sed -n '285,302p' papers/bedc/main.tex
```

Expected output around line 286:
```
\input/parts/concrete_instances/269_belief_namecert_construction.tex
... (other inputs)
\part{Ground Compiler Discipline}
\input{parts/ground_compiler.tex}
\part{Capstones}
\input{parts/capstones/index}
\part{Project Governance}
```

- [ ] **Step 2: Edit main.tex — remove Capstones part lines**

Use Edit tool to remove these two lines:

```
\part{Capstones}
\input{parts/capstones/index}
```

- [ ] **Step 3: Add 22 new `\input` lines after line 287 (the last existing concrete_instances line)**

Insert at the end of the existing `concrete_instances` `\input` block (after line `\input{parts/concrete_instances/269_belief_namecert_construction.tex}`):

```latex
\input{parts/concrete_instances/270_compact_uniform_continuity_namecert_construction.tex}
\input{parts/concrete_instances/271_compilation_morphism_namecert_construction.tex}
\input{parts/concrete_instances/272_computation_continuation_namecert_construction.tex}
\input{parts/concrete_instances/273_empty_fable_machine_namecert_construction.tex}
\input{parts/concrete_instances/274_halting_distinction_limit_namecert_construction.tex}
\input{parts/concrete_instances/275_inter_hist_locality_namecert_construction.tex}
\input{parts/concrete_instances/276_kernel_category_namecert_construction.tex}
\input{parts/concrete_instances/277_observer_hist_identity_namecert_construction.tex}
\input{parts/concrete_instances/278_real_completeness_namecert_construction.tex}
\input{parts/concrete_instances/279_reasoning_contradiction_boundary_namecert_construction.tex}
\input{parts/concrete_instances/280_reflection_limits_namecert_construction.tex}
\input{parts/concrete_instances/281_riemann_hypothesis_namecert_construction.tex}
\input{parts/concrete_instances/282_taste_gate_namecert_construction.tex}
\input{parts/concrete_instances/283_three_axioms_closure_namecert_construction.tex}
\input{parts/concrete_instances/284_type_checking_classifier_namecert_construction.tex}
\input{parts/concrete_instances/axiszeckendorf/unary_direction_bridge.tex}
\input{parts/concrete_instances/axiszeckendorf/zeckendorf_carry_classifier.tex}
\input{parts/concrete_instances/axiszeckendorf/axis_zeckendorf_cannot_claim.tex}
\input{parts/concrete_instances/real_completeness/transported_stationary_diagonal.tex}
\input{parts/concrete_instances/rh/contour_integral_operation.tex}
\input{parts/concrete_instances/rh/analytic_continuation_operation.tex}
\input{parts/concrete_instances/rh/zeta_continuation_application.tex}
```

- [ ] **Step 4: Verify main.tex no longer references capstones**

```bash
grep -n "capstones" papers/bedc/main.tex
```

Expected: empty.

### Task 1.7: Delete capstones/ directory remnants

**Files:**
- Delete: `papers/bedc/parts/capstones/` (everything left: index.tex, _index_files.tex, empty subdirs)

- [ ] **Step 1: List remaining capstones content**

```bash
find papers/bedc/parts/capstones -type f
```

Expected: just `index.tex` and `_index_files.tex` (subdir files moved out).

- [ ] **Step 2: Delete the index files and remove directory**

```bash
git rm papers/bedc/parts/capstones/index.tex
git rm papers/bedc/parts/capstones/_index_files.tex
# Remove empty subdirs
rmdir papers/bedc/parts/capstones/axiszeckendorf 2>/dev/null
rmdir papers/bedc/parts/capstones/real_completeness 2>/dev/null
rmdir papers/bedc/parts/capstones/rh 2>/dev/null
rmdir papers/bedc/parts/capstones 2>/dev/null
```

- [ ] **Step 3: Verify directory is gone**

```bash
ls papers/bedc/parts/capstones 2>&1
```

Expected: `No such file or directory`.

### Task 1.8: Run all 5 verification gates

**Files:** None (read-only checks)

- [ ] **Step 1: lake build (Lean compile)**

```bash
cd /Users/auric/newmath/lean4 && lake build 2>&1 | tail -3 && cd ..
```

Expected: `Build completed successfully (NNNN jobs)`. If fails, common cause is namespace not fully migrated — check error and re-run sed for Task 1.4.

- [ ] **Step 2: Axiom audit**

```bash
python3 tools/check-axioms.py
```

Expected: `Axiom audit: 0 axioms in lean4/BEDC/. Project invariant holds.`

- [ ] **Step 3: bedc_ci audit (paper ↔ Lean drift)**

```bash
python3 lean4/scripts/bedc_ci.py audit 2>&1 | tail -2
```

Expected: `[bedc-ci] audit: lean_files=N declarations=N part_labels=N lean_markers=N`. If a `\leanchecked` references missing target, the audit will report it.

- [ ] **Step 4: axiom-purity --strict (transitive deps)**

```bash
python3 lean4/scripts/bedc_ci.py axiom-purity --strict 2>&1 | tail -2
```

Expected: `[bedc-ci] axiom-purity: theorems=N pure=N impure=0 forbidden=...`. Any `impure>0` means a propext/Classical.choice/Quot.sound leak — must fix before commit.

- [ ] **Step 5: paper double-pass build (resolves all autoref)**

```bash
cd /Users/auric/newmath/papers/bedc && make 2>&1 | tail -10 && cd ../..
```

Expected: PDF generated, no `?? on page ??` in TOC, no broken `\autoref`. **Critical** — this catches any `\label`/`\autoref` mismatch from Task 1.4 sed.

If any `?? on page ??` appears, grep the produced log for `LaTeX Warning: Reference` and fix the dangling labels.

### Task 1.9: Commit Phase 1 atomically

**Files:** All changes from Tasks 1.1-1.8

- [ ] **Step 1: Inspect what's staged**

```bash
git status --short | wc -l
git diff --stat HEAD | tail -5
```

Expected: ~30+ files in status (15 mv + 7 mv + 2 lean + main.tex + index removals + sed changes throughout).

- [ ] **Step 2: Stage everything and commit**

```bash
git add -A
git commit -m "$(cat <<'EOF'
refactor: physically merge capstones into concrete_instances (flat)

Capstones are NameCert constructions, no different in schema from other
concrete instances. This removes the artificial separation and makes
schema-uniformity visible in directory structure: every BEDC paper
chapter is one NameCert.

- 15 top-level capstone files → concrete_instances/270-284_*_namecert_construction.tex
- 3 capstone subdirs (axiszeckendorf/, real_completeness/, rh/, total 7 files)
  → concrete_instances/<same-subdir>/ (subdirs created)
- Lean modules: BEDC.Capstone.* → BEDC.Derived.*
  (EmptyFableMachine moved, Capstone.lean removed)
- main.tex: \part{Capstones} removed, 22 new \input lines added under
  existing concrete_instances block
- 38 cross-章 \autoref + 30 internal + 27 \leanchecked markers re-pathed
  via sed (ch:capstones-X → ch:concrete-instances-X; BEDC.Capstone → BEDC.Derived)
- All five gates pass: lake build, check-axioms, bedc_ci audit,
  axiom-purity --strict, make (full double-pass)

Phase 1 of two-phase migration: this commit only moves files and fixes
references. Phase 2 (per-chapter NameCert 5-tuple rewrite + closurestatus
addition) follows in subsequent commits on the same branch.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

- [ ] **Step 3: Push**

```bash
git push origin capstones-physical-migration
```

---

## Phase 2: Per-Chapter NameCert 5-tuple Rewrite

Each of the 22 migrated chapters becomes its own task. They share a common template documented once below; per-chapter tasks reference it.

### Common Template: NameCert 5-tuple Rewrite

For each migrated chapter at `<new_path>` with target NameCert object `<X>Up`:

The chapter must end up with the following structure:

```latex
\chapter{Naming Certificate for <X>Up}
\label{ch:concrete-instances-<slug>}

[1-2 sentence chapter motivation: what mathematical / meta object this names,
 and why it merits a NameCert.]

\section{Source spec for <X>Up}
\label{sec:concrete-instances-<slug>-source-spec}

\begin{definition}[Source rows of <X>Up]
\label{def:concrete-instances-<slug>-source-rows}
[Define the SourceSpec — what tuples / event-flow data feed this NameCert.
 For a bridge-type capstone, the source rows are tuples (objA, objB, ...,
 bridge_witness). For a meta-type capstone, the source rows are instances
 of the meta-pattern.]
\end{definition}
\leandef{BEDC.Derived.<X>Up.SourceRows}

\section{Pattern spec}
\label{sec:concrete-instances-<slug>-pattern}

\begin{definition}[Pattern witness for <X>Up]
\label{def:concrete-instances-<slug>-pattern}
[Define the PatternSpec — the recognizable shape that all source rows
 share. For bridges this is the structural correspondence; for meta
 capstones this is the schematic move.]
\end{definition}
\leandef{BEDC.Derived.<X>Up.Pattern}

\section{Classifier spec}
\label{sec:concrete-instances-<slug>-classifier}

\begin{definition}[Classifier for <X>Up]
\label{def:concrete-instances-<slug>-classifier}
[Define the ClassifierSpec — when two source rows name the same <X>Up
 element. This is the equivalence at the named-object level.]
\end{definition}
\leandef{BEDC.Derived.<X>Up.Classifier}

\section{Stability certificate}
\label{sec:concrete-instances-<slug>-stability}

\begin{theorem}[Stability of <X>Up]
\label{thm:concrete-instances-<slug>-stability}
[State and prove that <X>Up is closed under the relevant operations
 (composition, transport, restriction, etc.). For bridges, this is
 closure under the bridged structure's operations. For meta capstones,
 closure under scheme-substitution / meta-instantiation.]
\end{theorem}
\leanchecked{BEDC.Derived.<X>Up.stability}

\section{Ledger policy}
\label{sec:concrete-instances-<slug>-ledger}

\begin{definition}[Ledger for <X>Up]
\label{def:concrete-instances-<slug>-ledger}
[Define the LedgerPolicy — what raw histories / source data are kept
 to bind classified objects back to their generators.]
\end{definition}
\leandef{BEDC.Derived.<X>Up.Ledger}

[OPTIONAL: any chapter-specific theorems or remarks that don't fit the
 5 sections, prefixed with \section{Ancillary results}. Bridge capstones
 typically have a "main bridge theorem" that goes here.]

\begin{closurestatus}{<X>Up}
  \theoryclosure{\scopedClosure}
  \scopeclosed{<one sentence: what is closed at this scope>}
  \formalstatus{\theoremCheckedV}
  \leantarget{BEDC.Derived.<X>Up.<canonical_target>}
  \bridgestatus{none}
  \notclaimed{<one sentence: what this chapter explicitly does not claim>}
  \upgradepath{<one sentence: what would push to next closure level>}
\end{closurestatus}
```

The corresponding Lean file `lean4/BEDC/Derived/<X>Up.lean` (or extension of existing if the object already has a derived module) provides the 5 named declarations:

```lean
-- lean4/BEDC/Derived/<X>Up.lean
import BEDC.FKernel  -- whatever the chapter actually needs

namespace BEDC.Derived.<X>Up

def SourceRows : Type := <type>
def Pattern (s : SourceRows) : Prop := <prop>
def Classifier (s t : SourceRows) : Prop := <prop>
theorem stability : <stability statement> := by
  <proof, MUST be axiom-pure>
def Ledger : Type := <type>

end BEDC.Derived.<X>Up
```

### Per-chapter task structure (template — apply 22 times)

For each chapter, the task structure is:

````markdown
### Task 2.N: NameCert rewrite for <X>Up

**Files:**
- Modify: `<new_path>` (rewrite as 5-tuple per template)
- Create or extend: `lean4/BEDC/Derived/<X>Up.lean` (5 named declarations)
- Test: `papers/bedc && make` + 5 gates

- [ ] **Step 1: Read current chapter content**

```bash
cat <new_path>
```

Identify in the prose: (a) the named higher-order object, (b) the constituent tuples / source data, (c) the structural pattern, (d) the equivalence / classifier, (e) what closure / stability is implied.

- [ ] **Step 2: Draft Lean file**

Create `lean4/BEDC/Derived/<X>Up.lean` with the 5 declarations sketched. The proofs MUST be axiom-pure (no `propext`, `Classical.choice`, `Quot.sound`, `simp`-with-iff).

- [ ] **Step 3: Add umbrella import**

Add `import BEDC.Derived.<X>Up` to `lean4/BEDC.lean` (in alphabetical position).

- [ ] **Step 4: Run lake build to verify Lean compiles**

```bash
cd lean4 && lake build BEDC.Derived.<X>Up 2>&1 | tail -3 && cd ..
```

Expected: builds clean. If propext leaks, refactor proof to avoid `simp` / `Iff` rewrite.

- [ ] **Step 5: Verify per-theorem axiom purity**

```bash
cd lean4 && echo "#print axioms BEDC.Derived.<X>Up.stability" | lake env lean --stdin && cd ..
```

Expected: no axioms shown beyond `[implementation]`.

- [ ] **Step 6: Rewrite the .tex file using the template**

Use Edit tool to replace the existing chapter content with the 5-tuple template. Preserve `\label{ch:concrete-instances-<slug>}` (unchanged from Phase 1).

- [ ] **Step 7: Add closurestatus block at end of .tex**

Append the closurestatus block (per template) before the final paragraph or after the last section.

- [ ] **Step 8: Run all 5 gates**

```bash
cd /Users/auric/newmath/lean4 && lake build && cd ..
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity --strict
cd papers/bedc && make check && cd ../..
```

All must exit 0.

- [ ] **Step 9: Commit**

```bash
git add <new_path> lean4/BEDC/Derived/<X>Up.lean lean4/BEDC.lean
git commit -m "namecert: rewrite <X>Up chapter as 5-tuple + closurestatus

- Source/Pattern/Classifier/Stability/Ledger sections per NameCert template
- Lean module BEDC.Derived.<X>Up with 5 named declarations, axiom-pure
- closurestatus block: \\theoremCheckedV / \\scopedClosure
- All five gates pass

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>"

git push origin capstones-physical-migration
```
````

### Phase 2 task list (apply template above to each)

- [ ] **Task 2.1:** RealCompletenessUp (`278_real_completeness_namecert_construction.tex` → `BEDC.Derived.RealCompletenessUp`)
  - Source rows: pairs `(regular_cauchy_seq, modulus)` over `RegSeqRat`
  - Pattern: regular sequence regularity bound
  - Classifier: `psame` on diagonal limits
  - Stability: closed under arithmetic in `NameCert_RealUp`
  - Ledger: approximation bound trace

- [ ] **Task 2.2:** CompactUniformContinuityUp (`270_..._namecert_construction.tex`)
  - Source rows: triples `(K_compact, f_continuous_on_K, modulus_omega)`
  - Pattern: uniform continuity witness on compact
  - Classifier: agreement on shared compact subset
  - Stability: closed under restriction to compact subsets
  - Ledger: compact-subset enumeration trace

- [ ] **Task 2.3:** CompilationMorphismUp (`271_compilation_morphism_namecert_construction.tex`)
  - Source rows: `(event_flow_input, channel_stream_output, compile_witness)`
  - Pattern: compile/decode round-trip preservation
  - Classifier: morphism equality (same input → same output up to channel-equiv)
  - Stability: closed under composition
  - Ledger: per-event compilation trace

- [ ] **Task 2.4:** ComputationContinuationUp (`272_computation_continuation_namecert_construction.tex`)
  - Source rows: `(initial_history, mark_sequence, continuation_history)`
  - Pattern: `Cont` kernel relation witness
  - Classifier: same-continuation up to `hsame`
  - Stability: closed under associativity
  - Ledger: continuation step trace

- [ ] **Task 2.5:** EmptyFableMachineUp (`273_empty_fable_machine_namecert_construction.tex`)
  - Source rows: machine traces with empty-fable structure
  - Pattern: empty-fable closure pattern
  - Classifier: trace equivalence
  - Stability: closed under sub-trace
  - Ledger: trace enumeration
  - Note: existing Lean module `BEDC.Derived.EmptyFableMachine` (post-Phase 1) — extend it to add 5-tuple structure

- [ ] **Task 2.6:** HaltingDistinctionLimitUp (`274_halting_distinction_limit_namecert_construction.tex`)
  - Source rows: `(machine, input, halt_step_or_diverge_witness)`
  - Pattern: halting as distinction-limit pattern
  - Classifier: same halting behavior
  - Stability: closed under simulation
  - Ledger: step-count trace

- [ ] **Task 2.7:** InterHistLocalityUp (`275_inter_hist_locality_namecert_construction.tex`)
  - Source rows: `(history_a, history_b, locality_witness)`
  - Pattern: inter-history locality structure
  - Classifier: locality-equivalence
  - Stability: closed under history extension preserving locality
  - Ledger: locality bound trace

- [ ] **Task 2.8:** KernelCategoryUp (`276_kernel_category_namecert_construction.tex`)
  - Source rows: `(obj_source, obj_target, morphism_witness)` where objects are FKernel structures
  - Pattern: composition pattern
  - Classifier: morphism-equivalence
  - Stability: closed under composition + identity
  - Ledger: composition chain trace

- [ ] **Task 2.9:** ObserverHistIdentityUp (`277_observer_hist_identity_namecert_construction.tex`)
  - Source rows: `(observer, history, identity_witness)`
  - Pattern: observer-as-history pattern
  - Classifier: same observer up to history-identity
  - Stability: closed under observation extension
  - Ledger: observer event trace

- [ ] **Task 2.10:** ReasoningContradictionBoundaryUp (`279_reasoning_contradiction_boundary_namecert_construction.tex`)
  - Source rows: contradiction-boundary instance triples
  - Pattern: contradiction-as-boundary pattern (BEDC's reading of double-negation elimination boundary)
  - Classifier: same boundary type
  - Stability: closed under sub-context
  - Ledger: contradiction position trace

- [ ] **Task 2.11:** ReflectionLimitsUp (`280_reflection_limits_namecert_construction.tex`)
  - Source rows: meta-loop reflection instances (the "two loops" structure)
  - Pattern: reflection schema
  - Classifier: same reflection layer
  - Stability: closed under reflection composition
  - Ledger: reflection ledger

- [ ] **Task 2.12:** RiemannHypothesisUp (`281_riemann_hypothesis_namecert_construction.tex`)
  - Source rows: `(zeta_zero, critical_strip_witness, real_part_witness)`
  - Pattern: critical-line membership pattern
  - Classifier: same-zero up to numerical equivalence in `ZetaZerosUp`
  - Stability: closed under analytic continuation
  - Ledger: contour-integral trace

- [ ] **Task 2.13:** TasteGateUp (`282_taste_gate_namecert_construction.tex`)
  - Source rows: theory-stability assessments (instances of "should we work on this")
  - Pattern: taste-gate criteria pattern
  - Classifier: same-judgment
  - Stability: closed under refinement
  - Ledger: judgment trace

- [ ] **Task 2.14:** MetaClosureMoveUp (`283_three_axioms_closure_namecert_construction.tex`)
  - Source rows: three axiom-instances (AC, Quot.sound, propext)
  - Pattern: "accept unwitnessed ∃ as input" schematic move
  - Classifier: equivalence of schematic moves
  - Stability: closed under syntactic substitution
  - Ledger: instance-axiom mapping
  - **Note:** This is the most subtle — be careful not to accidentally introduce the very axioms it discusses.

- [ ] **Task 2.15:** TypeCheckingClassifierUp (`284_type_checking_classifier_namecert_construction.tex`)
  - Source rows: `(term, classifier_membership_witness)`
  - Pattern: type-checking-as-classifier-membership pattern
  - Classifier: same-type up to classifier equivalence
  - Stability: closed under term substitution
  - Ledger: type-check trace

- [ ] **Task 2.16:** UnaryDirectionBridgeUp (`axiszeckendorf/unary_direction_bridge.tex`)
  - Source rows: `(unary_history, zeckendorf_witness, direction_bridge)`
  - Pattern: unary-to-Zeckendorf bridge
  - Classifier: same direction up to bridge-equiv
  - Stability: closed under unary extension
  - Ledger: bridge-step trace

- [ ] **Task 2.17:** ZeckendorfCarryClassifierUp (`axiszeckendorf/zeckendorf_carry_classifier.tex`)
  - Source rows: carry-classifier instances over Zeckendorf representation
  - Pattern: carry-classifier schema
  - Classifier: classifier equivalence
  - Stability: closed under carry-step
  - Ledger: carry-event trace

- [ ] **Task 2.18:** AxisZeckendorfCannotClaimUp (`axiszeckendorf/axis_zeckendorf_cannot_claim.tex`)
  - Source rows: cannot-claim records for axis Zeckendorf chapter
  - Pattern: cannot-claim recognition
  - Classifier: same cannot-claim entry
  - Stability: closed under chapter-extension
  - Ledger: cannot-claim register

- [ ] **Task 2.19:** TransportedStationaryDiagonalUp (`real_completeness/transported_stationary_diagonal.tex`)
  - Source rows: `(stationary_diagonal, transport_witness, target_history)`
  - Pattern: transport pattern for stationary diagonals
  - Classifier: same diagonal up to transport
  - Stability: closed under transport composition
  - Ledger: transport step trace

- [ ] **Task 2.20:** ContourIntegralOperationUp (`rh/contour_integral_operation.tex`)
  - Source rows: `(contour, integrand, integral_witness)`
  - Pattern: contour-integral operation pattern
  - Classifier: same integral value up to deformation
  - Stability: closed under contour deformation
  - Ledger: deformation chain

- [ ] **Task 2.21:** AnalyticContinuationOperationUp (`rh/analytic_continuation_operation.tex`)
  - Source rows: `(local_function, continuation_path, extended_function)`
  - Pattern: analytic continuation chain pattern
  - Classifier: same continuation up to path-homotopy in domain
  - Stability: closed under continuation composition
  - Ledger: continuation chain

- [ ] **Task 2.22:** ZetaContinuationApplicationUp (`rh/zeta_continuation_application.tex`)
  - Source rows: zeta-continuation application instances
  - Pattern: zeta application pattern
  - Classifier: same application target
  - Stability: closed under domain restriction
  - Ledger: application trace

---

## Phase 3: Final Validation + PR + Merge

### Task 3.1: Final repo-wide validation

**Files:** None

- [ ] **Step 1: Re-run all 5 gates from clean state**

```bash
cd /Users/auric/newmath
git status --short  # expected: clean
cd lean4 && lake clean && lake build 2>&1 | tail -3 && cd ..
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit 2>&1 | tail -2
python3 lean4/scripts/bedc_ci.py axiom-purity --strict 2>&1 | tail -2
cd papers/bedc && make 2>&1 | tail -10 && cd ../..
```

Expected: all exit 0; PDF builds; impure=0.

- [ ] **Step 2: Manually skim the generated PDF**

Open `papers/bedc/main.pdf` and verify:
- Capstones chapters appear under "Concrete Instances" part (not their own part)
- TOC shows them as chapters numbered after `269_belief`
- No `?? on page ??` placeholders
- Spot-check 2-3 cross-references actually link

- [ ] **Step 3: Verify capstones/ is fully gone**

```bash
ls papers/bedc/parts/capstones 2>&1
grep -rE 'BEDC\.Capstone|parts/capstones|capstones-' papers/ lean4/ 2>/dev/null | grep -v Binary | head -5
```

Expected: directory not found; grep returns 0 lines (anything in committed files referencing the old structure is a bug).

### Task 3.2: Pre-flight CI check

**Files:** None

- [ ] **Step 1: Verify origin/auto-dev hasn't moved a lot during Phase 2**

```bash
git fetch origin auto-dev
git log --oneline HEAD..origin/auto-dev | wc -l
```

If 0-50 commits behind: proceed. If >50, merge origin/auto-dev first to avoid PR conflict:

```bash
git merge origin/auto-dev --no-edit
# Re-run all 5 gates after merge
```

- [ ] **Step 2: Confirm push is up-to-date**

```bash
git status
git push origin capstones-physical-migration
```

### Task 3.3: Open PR

**Files:** None

- [ ] **Step 1: Create PR with comprehensive description**

```bash
gh pr create --base auto-dev --head capstones-physical-migration \
  --title "refactor: unify capstones into concrete_instances as NameCerts" \
  --body "$(cat <<'EOF'
## Summary

Capstones are NameCert constructions, no different in schema from other concrete instances. This PR removes the artificial separation in two phases:

**Phase 1 (commit 1):** Physical migration. 22 files moved from `papers/bedc/parts/capstones/` to `papers/bedc/parts/concrete_instances/` (15 top-level + 7 in 3 subdirs), Lean modules `BEDC.Capstone.*` renamed to `BEDC.Derived.*`, all cross-refs and `\input` paths sed-rewritten, main.tex `\part{Capstones}` removed.

**Phase 2 (commits 2-23):** Per-chapter NameCert 5-tuple rewrite. Each migrated chapter restructured as Source / Pattern / Classifier / Stability / Ledger sections with corresponding `BEDC.Derived.<X>Up` Lean module providing 5 named declarations, plus `closurestatus` block at chapter end.

## Impact

- Schema-uniformity made visible: every BEDC paper chapter is one NameCert
- 22 new high-order NameCerts: bridge-type (RealCompletenessUp, RiemannHypothesisUp, ...), morphism-type (CompilationMorphismUp, KernelCategoryUp, ...), meta-type (MetaClosureMoveUp, TasteGateUp, ReflectionLimitsUp, ...)
- `\part{Capstones}` chapter division removed from main.tex
- Lean namespace flattened: no more `BEDC.Capstone` prefix

## Verification

All 5 gates pass on every commit:
- `cd lean4 && lake build` (axiom-free build)
- `python3 tools/check-axioms.py` (0 axioms)
- `python3 lean4/scripts/bedc_ci.py audit` (paper ↔ Lean drift = 0)
- `python3 lean4/scripts/bedc_ci.py axiom-purity --strict` (impure=0; no propext/Classical.choice/Quot.sound)
- `cd papers/bedc && make` (PDF double-pass; all `\autoref` resolve)

## Test plan

- [ ] CI: Lean4 build green
- [ ] CI: PDF build green
- [ ] CI: Detect relevant changes pass
- [ ] CI: Gate pass
- [ ] Local: PDF skim — all 22 chapters appear under Concrete Instances part
- [ ] Local: spot-check 3 random `\autoref` from outside chapters resolve correctly

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

- [ ] **Step 2: Note PR number**

```bash
gh pr view --json number --jq .number
```

Save it (e.g. PR #54).

### Task 3.4: Wait for CI green and merge

**Files:** None

- [ ] **Step 1: Watch CI**

```bash
gh pr checks <PR_NUMBER>
```

Expected (after ~5 min): 4 checks pass (Detect / Gate / Lean4 / PDF). If any fail, fix on branch, push, repeat.

- [ ] **Step 2: Merge with merge commit (per CLAUDE.md "git merge, never rebase")**

```bash
gh pr merge <PR_NUMBER> --merge
```

- [ ] **Step 3: Verify merge**

```bash
gh pr view <PR_NUMBER> --json state,mergedAt,mergeCommit
git fetch origin auto-dev
git log --oneline origin/auto-dev | head -3
```

Expected: state=MERGED, mergeCommit OID present, merge appears at top of auto-dev.

- [ ] **Step 4: Local cleanup**

```bash
git checkout auto-dev
git pull --ff-only origin auto-dev
git branch -d capstones-physical-migration
```

---

## Self-Review Checklist (run before starting Phase 1)

**1. Spec coverage:**
- ✅ Physical migration: covered in Phase 1 (Tasks 1.1-1.9)
- ✅ NameCert 5-tuple rewrite: covered in Phase 2 (template + 22 per-chapter tasks)
- ✅ Closurestatus addition: covered in Phase 2 template (final block of each .tex)
- ✅ Lean modules: rename in Phase 1 + 5-tuple decls in Phase 2
- ✅ Cross-refs: handled in Phase 1 sed
- ✅ main.tex: handled in Task 1.6

**2. Placeholder scan:**
- "TBD" / "TODO" / "implement later": NONE present
- "Add appropriate error handling": N/A (this is refactoring + content rewrite, no error paths)
- Per-chapter tasks (2.1-2.22) are templated — the template is fully spelled out, the per-chapter spec gives the specific Source/Pattern/Classifier/Stability/Ledger for each

**3. Type consistency:**
- All Lean namespaces use `BEDC.Derived.<X>Up` (consistent)
- All paper labels use `ch:concrete-instances-<slug>` (consistent)
- All `\leandef` / `\leanchecked` markers reference `BEDC.Derived.<X>Up.<member>` (consistent)
- Section subdivisions use `sec:concrete-instances-<slug>-{source-spec, pattern, classifier, stability, ledger}` (consistent)

## Known risks

1. **Codex-auto-dev parallel pipeline conflict.** The pipeline writes to `concrete_instances/` continuously. Phase 2 may push to the same files. Mitigation: pre-commit `git fetch + merge origin/auto-dev` per task. The branch `capstones-physical-migration` is held until end; periodic merge keeps drift small.

2. **Meta-capstone NameCert design (Tasks 2.10, 2.11, 2.13, 2.14) is conceptually fragile.** "What is the source spec of `MetaClosureMoveUp`?" requires careful design to avoid making the chapter vacuous. If a Phase 2 task feels like it's just renaming sections without real schema content, STOP and re-design rather than commit hollow content. Review with maintainer.

3. **Three axioms one closure (Task 2.14) must not introduce the very axioms it discusses.** The Lean module's `stability` proof must be axiom-pure. `axiom-purity --strict` will catch any leak.

4. **Subdir files (Tasks 2.16-2.22) currently lack `\chapter` markers** (they are typically `\section` within their parent's chapter context). Phase 2 must decide: promote to `\chapter` (each becomes its own TOC entry) or keep as `\section` under a parent chapter file. Default: promote to `\chapter` for consistency with the 5-tuple template; if user prefers section grouping, we add a parent file.

## Rollback

If Phase 1 fails verification, revert via:
```bash
git reset --hard origin/auto-dev  # destroys Phase 1 commit + push will need --force
```

If Phase 2 fails on a single chapter, revert just that chapter's commit:
```bash
git revert <chapter_commit_sha>
```

## Estimated effort

- Phase 0: 30 min (audit + branch verify)
- Phase 1: 3 hours (file mvs, sed, main.tex, gate debugging — main.tex `\input` ordering and `\part` removal often needs 2-3 iterations to settle)
- Phase 2: ~30 min per chapter × 22 = ~11 hours (mostly mechanical, but meta-capstones may take 2-3 hours each for design)
- Phase 3: 1 hour (PR, CI wait, merge)

**Total: ~16 hours of focused work.** Spread over 2-3 days realistic.
