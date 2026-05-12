# rule110 status

Status: Level 0 Behavioral Scaffold Complete.

This snapshot records the current citable state of the `rule110/` artifact.
The master plan is `ROADMAP.md`.

## Size

Command:

```bash
wc -l rule110/evaluator/*.c rule110/encoder/*.c rule110/tests/*.c
```

Report:

```text
      59 rule110/evaluator/cyclic_tag.c
      60 rule110/evaluator/rule110.c
     163 rule110/encoder/cook_collisions.c
      28 rule110/encoder/cook_construction.c
      45 rule110/encoder/cook_data_block.c
     290 rule110/encoder/cook_encode.c
      20 rule110/encoder/cook_glider_B.c
      20 rule110/encoder/cook_glider_C.c
      20 rule110/encoder/cook_glider_D.c
      20 rule110/encoder/cook_glider_E.c
      20 rule110/encoder/cook_glider_F.c
      20 rule110/encoder/cook_glider_G.c
      20 rule110/encoder/cook_glider_H.c
      31 rule110/encoder/cook_glider_gun.c
      24 rule110/encoder/cook_leader.c
      32 rule110/encoder/cook_ossifier.c
     101 rule110/encoder/groundcompiler_encoding.c
     364 rule110/tests/manifest_runner.c
     167 rule110/tests/test_ask.c
     588 rule110/tests/test_bundle.c
     120 rule110/tests/test_cont.c
      48 rule110/tests/test_cook_collisions.c
      89 rule110/tests/test_cook_data_block.c
     328 rule110/tests/test_cook_encode_arbitrary.c
      76 rule110/tests/test_cook_encode_empty.c
     159 rule110/tests/test_cook_encode_one.c
      67 rule110/tests/test_cook_ether.c
      94 rule110/tests/test_cook_glider_A.c
      73 rule110/tests/test_cook_glider_B.c
      73 rule110/tests/test_cook_glider_C.c
      73 rule110/tests/test_cook_glider_D.c
      98 rule110/tests/test_cook_glider_E.c
      98 rule110/tests/test_cook_glider_F.c
      98 rule110/tests/test_cook_glider_G.c
      98 rule110/tests/test_cook_glider_H.c
      84 rule110/tests/test_cook_glider_gun.c
      77 rule110/tests/test_cook_leader.c
     104 rule110/tests/test_cook_ossifier.c
     107 rule110/tests/test_cyclic_tag.c
     249 rule110/tests/test_encoder.c
     126 rule110/tests/test_ext.c
     370 rule110/tests/test_external_binary.c
     294 rule110/tests/test_gap.c
     311 rule110/tests/test_hist.c
      19 rule110/tests/test_manifest_runner_r110.c
     189 rule110/tests/test_mark.c
     333 rule110/tests/test_name_cert.c
     367 rule110/tests/test_package.c
     246 rule110/tests/test_round_trip.c
      61 rule110/tests/test_rule110.c
     646 rule110/tests/test_settled.c
     352 rule110/tests/test_sig.c
     259 rule110/tests/test_unary.c
    7878 total
```

Manifest count:

```bash
find rule110/manifests -name '*.ct' | wc -l
```

```text
      44
```

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

The current cyclic-tag manifest surface covers 13 FKernel modules:

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
== tests/test_round_trip ==
== test_round_trip ==
  round_trip_msame_refl_enum: SKIP (cook_encode returned 0 - production/tape shape not yet supported)
ALL test_round_trip tests passed
== tests/test_cook_encode_arbitrary ==
== test_cook_encode_arbitrary ==
  two_productions_empty_tape: PASS
  two_productions_five_bit_tape: PASS
  four_productions_three_bit_tape: PASS
  mark_manifest_productions: PASS
ALL test_cook_encode_arbitrary tests passed
ALL TESTS PASSED
```
