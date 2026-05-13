# rule110 status

Status: Tier A (cyclic-tag witness) **shipped**; Tier B (.enum.ct direct-carrier round-trip) **shipped**.

This snapshot records the current citable state of the `rule110/` artifact.
The master plan is `ROADMAP.md`.

## 框架 (2026-05-13 路线图 v3 之后)

详细见 `ROADMAP.md`. 简要:

- **Tier A 状态**: ship 完成. Tag `rule110-v2.0-fkernel-tier-a` at `d3ae91028`. 信任基 ≈ 250 行 C + 文本 manifest. Lean kernel 不在 trust path. `make test` exit 0, CI 全绿, 0 axiom invariant 保持. `papers/bedc/` external-witness 引用已接入.
- **Tier B 状态**: ship 完成 (`.enum.ct` 范围). Tag `rule110-v3.0-fkernel-tier-b`. 25 个 FKernel `.r110.ct` direct-carrier manifests, round-trip 全过. Martinez 2001 phase catalog + Martinez 2012 collision/soliton table 已接入 `encoder/glider_phases.c/h` + `encoder/martinez_2012_collisions.txt`. Cook packet phase-exact bodies (ossifier/leader/data_block) wired through canonical lookup. 信任路径降到 `evaluator/rule110.c` (~50 行) + `.r110` 文本.
- **不在 Tier B 范围**: `.algo.ct` (bounded recognizers, 不需要物理嵌入); Beyond-FKernel 4 模块 (appendix).

L4 cross-check / L5 Beyond-FKernel mirrors 重新定位为开发工具 / 附录, 见 ROADMAP §"Lean / L4 / L5 重新定位".

## Size

Command:

```bash
wc -l rule110/evaluator/*.c rule110/encoder/*.c rule110/tests/*.c
```

Report:

```text
      59 rule110/evaluator/cyclic_tag.c
      60 rule110/evaluator/rule110.c
     535 rule110/encoder/block_assembler.c
      32 rule110/encoder/cook_blocks.c
     463 rule110/encoder/cook_collisions.c
      39 rule110/encoder/cook_construction.c
     147 rule110/encoder/cook_data_block.c
     187 rule110/encoder/cook_decode.c
     543 rule110/encoder/cook_encode.c
      28 rule110/encoder/cook_glider_B.c
      32 rule110/encoder/cook_glider_C.c
      32 rule110/encoder/cook_glider_D.c
      29 rule110/encoder/cook_glider_E.c
      29 rule110/encoder/cook_glider_F.c
      29 rule110/encoder/cook_glider_G.c
      29 rule110/encoder/cook_glider_H.c
      40 rule110/encoder/cook_glider_gun.c
     193 rule110/encoder/cook_leader.c
     128 rule110/encoder/cook_ossifier.c
     330 rule110/encoder/generate_r110.c
     577 rule110/encoder/generate_r110_algo.c
     144 rule110/encoder/generate_r110_mark.c
     163 rule110/encoder/glider_phases.c
     610 rule110/encoder/glider_search.c
     101 rule110/encoder/groundcompiler_encoding.c
     106 rule110/encoder/phase_verifier.c
     364 rule110/tests/manifest_runner.c
     316 rule110/tests/test_ask.c
     687 rule110/tests/test_bundle.c
     250 rule110/tests/test_circle_up.c
     298 rule110/tests/test_cont.c
     133 rule110/tests/test_cook_collisions.c
     139 rule110/tests/test_cook_data_block.c
     354 rule110/tests/test_cook_encode_arbitrary.c
      76 rule110/tests/test_cook_encode_empty.c
     159 rule110/tests/test_cook_encode_one.c
      67 rule110/tests/test_cook_ether.c
     170 rule110/tests/test_cook_glider_A.c
      73 rule110/tests/test_cook_glider_B.c
      73 rule110/tests/test_cook_glider_C.c
      73 rule110/tests/test_cook_glider_D.c
      98 rule110/tests/test_cook_glider_E.c
      98 rule110/tests/test_cook_glider_F.c
      98 rule110/tests/test_cook_glider_G.c
      98 rule110/tests/test_cook_glider_H.c
      84 rule110/tests/test_cook_glider_gun.c
     120 rule110/tests/test_cook_leader.c
     150 rule110/tests/test_cook_ossifier.c
     118 rule110/tests/test_cook_packet_phase_exact.c
     107 rule110/tests/test_cyclic_tag.c
     249 rule110/tests/test_encoder.c
     314 rule110/tests/test_ext.c
     552 rule110/tests/test_external_binary.c
     326 rule110/tests/test_fold_up.c
     621 rule110/tests/test_gap.c
      87 rule110/tests/test_glider_phases.c
     420 rule110/tests/test_ground_compiler.c
     311 rule110/tests/test_hist.c
      19 rule110/tests/test_manifest_runner_r110.c
     189 rule110/tests/test_mark.c
     282 rule110/tests/test_meta_cic.c
     640 rule110/tests/test_name_cert.c
     685 rule110/tests/test_package.c
      28 rule110/tests/test_phase_verifier.c
     669 rule110/tests/test_r110_round_trip.c
      62 rule110/tests/test_rule110.c
     766 rule110/tests/test_settled.c
     745 rule110/tests/test_sig.c
     365 rule110/tests/test_topology_up.c
     312 rule110/tests/test_unary.c
   16510 total
```

Manifest counts:

```bash
find rule110/manifests -name '*.enum.ct' | wc -l
find rule110/manifests -name '*.algo.ct' | wc -l
find rule110/manifests \( -name '*.enum.ct' -o -name '*.algo.ct' \) | wc -l
find rule110/manifests -name '*.r110.ct' | wc -l
find rule110/manifests -name '*.algo.r110.ct' | wc -l
find rule110/manifests -name '*.ct' | wc -l
```

```text
      37
      22
      59
      59
      22
     118
```

The source manifest surface is 59 `.ct` files: 37 `.enum.ct` and 22
`.algo.ct`. The generated on-disk Rule 110 surface is 59 `.r110.ct`
files: 37 enum-derived plus 22 `.algo.r110.ct`. After `make test`
materializes generated manifests, the on-disk `.ct` total is 118.

## Test Case Count

The visible manifest and semantic assertion totals from `make test` are:

- 32 Mark cases.
- 470 extended module cases: 66 BHist hsame, 5 bounded BHist CT
  certificates, 16 Ext, 36 SigRel/sameSig, 20 Cont, 60 ProbeBundle,
  24 Ask, 43 ExternalBinary, 28 Gap, 38 Package, 58 NameCert, and 76
  Settled cases.
- 502 counted manifest/semantic cases total, plus pipeline smoke checks and
  Cook scaffold unit tests.

## Module Coverage

The current cyclic-tag manifest surface covers 13 FKernel modules plus
GroundCompiler:

- Mark
- Hist
- Ext
- SigRel and sameSig
- Cont
- Bundle
- Unary
- Ask
- ExternalBinary
- Gap
- Package
- NameCert
- Settled
- GroundCompiler

The current Rule 110 direct-carrier surface covers 37 `.r110.ct` manifests:
25 FKernel/GroundCompiler files plus 12 Beyond-FKernel appendix files. The
FKernel/GroundCompiler portion is Mark 4, Hist 5, Ext 1, Sig 2, Cont 1,
Bundle 2, Unary 1, Ask 1, ExternalBinary 1, Gap 1, Package 1, NameCert 1,
Settled 1, and GroundCompiler 3. The Beyond-FKernel portion is
`topology_up`, `fold_up`, `circle_up`, and `meta_cic`, three files each.
All source `.enum.ct` files have `PRODUCTIONS 0`. The generated carrier
cases cover every binary `input=` assertion; `ground_compiler/reject_reasons`
has two non-binary/display-only assertions outside direct carrier encoding.
The appendix modules are generated as `.r110.ct` files and are exercised by
`test_topology_up`, `test_fold_up`, `test_circle_up`, and `test_meta_cic`
inside `make test`.

## Deliberate Gaps

- Phase-exact Cook construction remains a Level 3 target. The current Rule
  110 side is a behavioral scaffold with ether, glider, leader, ossifier,
  data-block, and cyclic-tag encoder tests.
- Lean cross-checking remains a Level 4 target. The current artifact is a
  ground-up behavioral substrate, not a Lean equivalence proof.
- Universal algorithm recognizers remain a Level 2 target. Current `algo`
  manifests are executable behavioral fixtures; the arbitrary-recognizer layer
  is not claimed here.

## Verification

Command:

```bash
cd rule110 && make clean && make && make test
```

Result: exit 0. The final `make test` output is recorded below.

```text
== tests/test_rule110 ==
== test_rule110 ==
  single_step_known_pattern: PASS
  all_zero_stays_zero: PASS
  boundary_fixed_at_zero: PASS
  dump_state_format: PASS
ALL test_rule110 tests passed
== tests/test_cyclic_tag ==
== test_cyclic_tag ==
  identity_ct_halts_when_tape_empty: PASS
  simple_growth_then_halt: PASS
  steplimit_caught: PASS
ALL test_cyclic_tag tests passed
== tests/test_encoder ==
== test_encoder ==
  body_encode_b0: PASS
  body_encode_b1: PASS
  event_encode_b0: PASS
  event_encode_b1: PASS
  dec_event_roundtrip_b0: PASS
  dec_event_roundtrip_b1: PASS
  dec_event_reject_dangling_one: PASS
  dec_event_reject_unfinished: PASS
  dec_event_reject_resource_bound: PASS
  dec_event_reject_empty: PASS
  bhist_encode_empty: PASS
  bhist_encode_e0_empty: PASS
  bhist_encode_e1_empty: PASS
  bhist_encode_depth_3: PASS
  bhist_encode_depth_10: PASS
  bhist_encode_depth_100: PASS
  bhist_decode_roundtrip: PASS
  bhist_decode_reject_unfinished: PASS
ALL test_encoder tests passed
== tests/test_mark ==
== test_mark ==
  msame_refl.enum: 2/2 cases PASS
  msame_refl.algo: 2/2 cases PASS (vacuous productions, recognition via decoder)
  msame_symm.enum: 4/4 cases PASS
  msame_symm.algo: 4/4 cases PASS
  msame_trans.enum: 8/8 cases PASS
  msame_trans.algo: 8/8 cases PASS
  msame_no_confusion.enum: 2/2 cases PASS
  msame_no_confusion.algo: 2/2 cases PASS
  pipeline_smoke (8 manifests, all halt-empty in <=200 steps): PASS
ALL test_mark assertions passed (32 total + 8-manifest pipeline smoke)
== tests/test_cook_ether ==
== test_cook_ether ==
  ether_stable_under_rule110: PASS
  ether_emit_correct_length: PASS
ALL test_cook_ether tests passed
== tests/test_cook_glider_A ==
== test_cook_glider_A ==
  glider_A_emerges: PASS
  ether_remains_outside_glider: PASS
ALL test_cook_glider_A tests passed
== tests/test_cook_glider_E ==
== test_cook_glider_E ==
  glider_E_moves: PASS
  glider_E_ether_unaffected: PASS
ALL test_cook_glider_E tests passed
== tests/test_cook_glider_F ==
== test_cook_glider_F ==
  glider_F_moves: PASS
  glider_F_ether_unaffected: PASS
ALL test_cook_glider_F tests passed
== tests/test_cook_glider_G ==
== test_cook_glider_G ==
  glider_G_moves: PASS
  glider_G_ether_unaffected: PASS
ALL test_cook_glider_G tests passed
== tests/test_cook_glider_H ==
== test_cook_glider_H ==
  glider_H_moves: PASS
  glider_H_ether_unaffected: PASS
ALL test_cook_glider_H tests passed
== tests/test_cook_glider_gun ==
== test_cook_glider_gun ==
  glider_gun_emits_periodically: PASS
  glider_gun_ether_unaffected: PASS
ALL test_cook_glider_gun tests passed
== tests/test_cook_ossifier ==
== test_cook_ossifier ==
  ossifier_3bit_production: PASS
  ossifier_empty_production: PASS
ALL test_cook_ossifier tests passed
== tests/test_cook_data_block ==
== test_cook_data_block ==
  data_block_5bit_tape: PASS
  data_block_empty: PASS
ALL test_cook_data_block tests passed
== tests/test_hist ==
== test_hist ==
  hsame_refl.enum: 5/5 cases PASS
  hsame_refl.algo: 5/5 cases PASS (bounded CT marker certificates)
  hsame_symm.enum: 7/7 cases PASS
  hsame_symm.algo: 7/7 cases PASS
  hsame_empty_inversion.enum: 5/5 cases PASS
  hsame_empty_inversion.algo: 5/5 cases PASS
  hsame_trans.enum: 8/8 cases PASS
  hsame_trans.algo: 8/8 cases PASS
  hsame_constructor_distinct.enum: 12/12 cases PASS
  hsame_constructor_distinct.algo: 12/12 cases PASS
ALL test_hist assertions passed (66 BHist hsame cases + 3-manifest pipeline smoke + 5 bounded CT certificates)
== tests/test_ext ==
== test_ext ==
  ext_step.enum: 8/8 cases PASS
  ext_step.algo: 8/8 cases PASS
ALL test_ext assertions passed (16 Ext step cases + 2-manifest pipeline smoke)
== tests/test_sig ==
== test_sig ==
  sigrel_basic.enum: 9/9 cases PASS
  sigrel_basic.algo: 9/9 cases PASS
  samesig_equiv.enum: 9/9 cases PASS
  samesig_equiv.algo: 9/9 cases PASS
  pipeline_smoke (4 sig manifests, all halt-empty in <=200 steps): PASS
ALL test_sig assertions passed (36 semantic cases + 4-manifest pipeline smoke)
== tests/test_cont ==
== test_cont ==
  cont_basic.enum: 10/10 cases PASS
  cont_basic.algo: 10/10 cases PASS
ALL test_cont assertions passed (20 Cont cases + 2-manifest pipeline smoke)
== tests/test_bundle ==
== test_bundle ==
  bundle_length.enum: 14/14 cases PASS
  bundle_length.algo: 14/14 cases PASS
  bundle_membership.enum: 16/16 cases PASS
  bundle_membership.algo: 16/16 cases PASS
ALL test_bundle assertions passed (60 ProbeBundle cases + 4-manifest pipeline smoke)
== tests/test_unary ==
== test_unary ==
  unary_basic.enum: semantic cases PASS
  unary_basic.algo: semantic cases PASS
ALL test_unary assertions passed
== tests/test_ask ==
== test_ask ==
  ask_basic.enum: 12/12 cases PASS
  ask_basic.algo: 12/12 cases PASS
  pipeline_smoke (2 ask manifests, all halt-empty in <=200 steps): PASS
ALL test_ask assertions passed (24 Ask cases + 2-manifest pipeline smoke)
== tests/test_external_binary ==
== test_external_binary ==
  external_model_reuse: 3/3 cases PASS
  external_binary_basic.enum: 12/12 cases PASS
  external_binary_basic.algo: 12/12 cases PASS
  external_inversion: 10/10 cases PASS
  external_cancellation_congruence: 6/6 cases PASS
ALL test_external_binary assertions passed (43 ExternalBinary cases + 2-manifest pipeline smoke)
== tests/test_gap ==
== test_gap ==
  gap_basic.enum: 14/14 cases PASS
  gap_basic.algo: 14/14 cases PASS
ALL test_gap assertions passed (28 Gap cases + 2-manifest pipeline smoke)
== tests/test_package ==
== test_package ==
  package_basic.enum: 19/19 cases PASS
  package_basic.algo: 19/19 cases PASS
  pipeline_smoke (2 package manifests, all halt-empty in <=200 steps): PASS
ALL test_package assertions passed (38 Package cases + 2-manifest pipeline smoke)
== tests/test_name_cert ==
== test_name_cert ==
  name_cert_basic.enum: 29/29 cases PASS
  name_cert_basic.algo: 29/29 cases PASS
  pipeline_smoke (2 name_cert manifests, all halt-empty in <=200 steps): PASS
ALL test_name_cert assertions passed (58 NameCert cases + 2-manifest pipeline smoke)
== tests/test_settled ==
== test_settled ==
  settled_basic.enum: 38/38 cases PASS
  settled_basic.algo: 38/38 cases PASS
ALL test_settled assertions passed (76 Settled cases + 2-manifest pipeline smoke)
== tests/test_cook_glider_B ==
== test_cook_glider_B ==
  glider_B_moves: PASS
  glider_B_ether_unaffected: PASS
ALL test_cook_glider_B tests passed
== tests/test_cook_glider_C ==
== test_cook_glider_C ==
  glider_C_moves: PASS
  glider_C_ether_unaffected: PASS
ALL test_cook_glider_C tests passed
== tests/test_cook_glider_D ==
== test_cook_glider_D ==
  glider_D_moves: PASS
  glider_D_ether_unaffected: PASS
ALL test_cook_glider_D tests passed
== tests/test_cook_collisions ==
== test_cook_collisions ==
left right pos1 pos2 steps outcome
A A 420 560 220 passthrough
A B 420 560 220 passthrough
A C 420 560 220 passthrough
A D 420 560 220 passthrough
B A 420 560 220 passthrough
B B 420 560 220 passthrough
B C 420 560 220 passthrough
B D 420 560 220 passthrough
C A 420 560 220 passthrough
C B 420 560 220 passthrough
C C 420 560 220 annihilation
C D 420 560 220 passthrough
D A 420 560 220 passthrough
D B 420 560 220 passthrough
D C 420 560 220 passthrough
D D 420 560 220 passthrough
== tests/test_cook_leader ==
== test_cook_leader ==
  leader_stable: PASS
  leader_does_not_destroy_ether_outside: PASS
ALL test_cook_leader tests passed
== tests/test_cook_encode_empty ==
== test_cook_encode_empty ==
  cook_encode_empty: PASS
  cook_encode_empty_rejects_small_buffer: PASS
  cook_encode_non_empty_stub: PASS
ALL test_cook_encode_empty tests passed
== tests/test_manifest_runner_r110 ==
== test_manifest_runner_r110 ==
  synthetic_ether_manifest: PASS
ALL test_manifest_runner_r110 tests passed
== tests/test_cook_encode_one ==
== test_cook_encode_one ==
  one_production_empty_tape: PASS
  one_production_three_bit_tape: PASS
ALL test_cook_encode_one tests passed
== tests/test_cook_encode_arbitrary ==
== test_cook_encode_arbitrary ==
  two_productions_empty_tape: PASS
  two_productions_five_bit_tape: PASS
  four_productions_three_bit_tape: PASS
  mark_manifest_productions: PASS
ALL test_cook_encode_arbitrary tests passed
ALL TESTS PASSED
```
