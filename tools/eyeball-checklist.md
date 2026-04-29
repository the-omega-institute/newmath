# Migration Eyeball Checklist

Before .source/ deletion, the user must read each row, compare the new file against the source file, and sign off "OK <date>" in the Status column. The audit script catches lexical drift; this checklist catches semantic drift.

## Merged proof_obligations chapters (8 chapters; cross-version content fold)

| New chapter | Source files | Status |
|---|---|---|
| parts/proof_obligations/domain_policy.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_1/01_domain_policy.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_2/01_unary_domain_policy_instance.tex | TODO |
| parts/proof_obligations/package_token_policy.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_1/02_package_token_policy.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_2/02_inductive_package_token_policy.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_3/01_token_intro_uniqueness.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_4/02_token_uniqueness_modes.tex | TODO |
| parts/proof_obligations/gap_policy.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_1/03_gap_policy_consolidation.tex | TODO |
| parts/proof_obligations/psame_design.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_4/01_psame_design_contract.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/02_base_reflection_schema.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/04_closure_reflection_optional_target.tex | TODO |
| parts/proof_obligations/exact_globalize.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_3/02_exact_concrete_globalize.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_4/03_exactness_export_contract.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/01_checker_friendly_exactness.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/03_exact_globalize_base_contract.tex | TODO |
| parts/proof_obligations/unary_shift_and_commutativity.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_1/04_unary_commutativity_obligations.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_2/03_unary_shift_and_commutativity_hardening.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_3/03_unary_shift_micro_lemmas.tex | TODO |
| parts/proof_obligations/verification_queue.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_2/04_concrete_verification_targets.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_4/04_verification_queue.tex | TODO |
| parts/proof_obligations/lean_scaffold_contract.tex | .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/05_lean_scaffold_contract.tex | TODO |

## Frontmatter rewrites

| New file | Source | Status |
|---|---|---|
| frontmatter/status.tex | union of .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_5/06_status_matrix_v1_5_5.tex + .source/BEDC_Master_Project_v1_5_5/parts/proof_obligations_v1_5_4/05_status_matrix_v1_5_4.tex surviving rows | TODO |
| frontmatter/preface.tex | .source/BEDC_Master_Project_v1_5_5/frontmatter/preface.tex with version-narrative paragraphs dropped | TODO |
| frontmatter/roadmap.tex | .source/BEDC_Master_Project_v1_5_5/frontmatter/roadmap.tex with v1.4 footer dropped | TODO |

## Governance bundle

| File | Source | Status |
|---|---|---|
| parts/project_governance/governance.tex | .source/BEDC_Master_Project_v1_5_5/parts/project_governance/00_version_governance.tex with active-mode header | TODO |
| parts/project_governance/migration_index.tex | .source/BEDC_Master_Project_v1_5_5/parts/project_governance/01_migration_index.tex with active-mode framing | TODO |
| parts/project_governance/HOW_INCREMENT_WORKS.md | NEW (no source) — verify recipe is concrete and complete | TODO |

## Lean BaseReflection.lean

| File | Source | Status |
|---|---|---|
| lean4/BEDC/BaseReflection.lean | .source/BEDC_Master_Project_v1_5_5/lean/BEDC_v1_5_5_BaseReflection_Scaffold.lean | TODO |
| Verify: 12 axiom carriers preserved | (Hist, SigObj, Pkg, Pi, Domain, Evidence + relations + structures) | TODO |
| Verify: PackageReflection_base has REAL proof (not sorry) | source: lines 54-63 | TODO |
| Verify: PsameBase_inversion sorry'd with v0.2-redesign comment | (Lean 4 strict mode incompatibility) | TODO |
| Verify: ExactGlobalizeBase_classify_iff sorry'd with v0.2-redesign comment | (same reason) | TODO |

## Sign-off rule

Update each row's Status column to `OK YYYY-MM-DD` after checking. The finalize-migration.sh script greps this file for `TODO` and refuses to proceed until 0 TODOs remain.
