# Settled Design

Target: encode the executable proof-boundary surface of
`BEDC.FKernel.Settled`.

## Lean Shape

`Settled.lean` defines `SettledKernelCriterion` as a single conjunction of the
currently closed FKernel targets. It then exposes projections for the main
boundary families:

- history kernel: mark equivalence, mark no-confusion, history equivalence, and
  constructor inversion;
- Ext and Cont: determinacy, unit laws, and associativity up to `hsame`;
- signature kernel: SigRel determinacy and SameSig equivalence fields;
- package and gap: token witnesses, gap coverage, and composite coverage;
- globalize exactness: `psame` iff signature sameness under gap membership;
- unary name certificates: Nat-up and additive naming certificate existence;
- function-like descent: maps respecting source equality descend to targets;
- bundle generation: every bundle is nil or cons.

The settled module does not introduce a new primitive relation. Its role is to
bundle already exposed proof obligations into one proof-boundary criterion and
to make the projections available from that criterion.

## Ground Fixture

The rule110 manifest mirrors that role with a tagged aggregator:

```text
tag(family) ++ tag(case) ++ family payload
```

Both tags are unary natural-number events. The payloads reuse the concrete
fixtures from sibling modules:

- BHist events from `bhist_encoding.md`;
- Ext and Cont predicates from `ext_design.md` and `cont_design.md`;
- ProbeBundle, SigRel, and SameSig fixtures from `sigrel_design.md`;
- Gap domain/token fixtures from `gap_design.md`;
- Unary-history and additive certificate fixtures from `unary_design.md`.

The family tags are:

```text
0 history kernel
1 ext/cont kernel
2 signature kernel
3 package/gap kernel
4 globalize exactness
5 composite gap
6 name certificates
7 function descent
8 bundle generation
```

## Executable Checks

`tests/test_settled.c` decodes the two tags and dispatches to the corresponding
fixture checker. The cases are representative rather than exhaustive, because
the Lean theorem is a proof aggregator over abstract typeclasses. The C harness
checks the executable content behind each projection family:

- self-equality and constructor-distinct representatives for marks and
  histories;
- Ext determinacy by checking two results for the same input and mark;
- Cont determinacy, left/right unit laws, and an associativity witness;
- SigRel determinacy as a conditional theorem and SameSig symmetry/transitivity
  representatives;
- InGapSig coverage and package-token transport under the BHist package
  fixture;
- globalize exactness by comparing package equality with computed signature
  equality;
- composite coverage by carrying explicit middle/final witnesses and relation
  bits;
- unary name-certificate fields through unary carrier checks and classifier
  transport;
- function-like descent as a fixture map that preserves BHist equality;
- bundle generation by requiring a well-formed nil or cons bundle.

`settled_basic.enum.ct` lists the audit cases. `settled_basic.algo.ct` uses the
current vacuous cyclic-tag production pattern while the semantic checks live in
the C harness, matching the established abstract-boundary modules.

## Covered Cases

The manifest covers 38 cases:

- 6 history-kernel representatives;
- 6 Ext/Cont representatives;
- 4 signature-kernel representatives;
- 5 package/gap representatives;
- 4 globalize representatives;
- 2 composite-gap representatives;
- 6 name-certificate representatives;
- 2 function-descent representatives;
- 3 bundle-generation representatives.

Each manifest is smoke-tested through the cyclic-tag runner, and each semantic
case is checked once through the enum path and once through the algo path.

## Lean Theorem Alignment

The harness aligns with these `Settled.lean` targets:

- `settledKernelCriterion_from_current_targets`;
- `settledKernelCriterion_history_kernel_projection`;
- `settledKernelCriterion_ext_cont_projection`;
- `settledKernelCriterion_signature_kernel_projection`;
- `settledKernelCriterion_signature_determinacy_projection`;
- `settledKernelCriterion_sameSig_equivalence_projection`;
- `settledKernelCriterion_package_gap_projection`;
- `settledKernelCriterion_gap_coverage_projection`;
- `settledKernelCriterion_globalize_exactness_projection`;
- `settledKernelCriterion_composite_gap_projection`;
- `settledKernelCriterion_namecert_projection`;
- `layer_isolation_policy_memory_projection`;
- `settledKernelCriterion_function_like_descent_projection`;
- `settledKernelCriterion_bundle_generation_projection`;
- `settledKernelCriterion_milestoneB_signature_kernel`;
- `settledKernelCriterion_milestoneC_package_gap_kernel`.
