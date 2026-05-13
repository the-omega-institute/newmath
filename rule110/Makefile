# rule110 — BEDC ground-up minimal-trust vertical slice
# zero external deps, ANSI C99

CC      ?= cc
CFLAGS  ?= -std=c99 -O2 -Wall -Wextra -Wpedantic -Wshadow -Wno-unused-parameter
LDFLAGS ?=

EVAL_DIR    := evaluator
ENCODER_DIR := encoder
TEST_DIR    := tests
TOOLS_DIR   := tools

# Only rule110 evaluator ships as a standalone binary (with STANDALONE_MAIN).
# cyclic_tag and groundcompiler_encoding are libraries compiled into test binaries.
STANDALONE_BINS := $(EVAL_DIR)/rule110
ENCODER_BINS    := $(ENCODER_DIR)/generate_r110 $(ENCODER_DIR)/generate_r110_algo
TOOLS           := $(TOOLS_DIR)/manifest_exhaustiveness_audit
VISUALIZATION_TOOL := $(TOOLS_DIR)/visualize_rule110
TESTS           := $(TEST_DIR)/test_rule110 $(TEST_DIR)/test_cyclic_tag \
                   $(TEST_DIR)/test_encoder $(TEST_DIR)/test_mark \
                   $(TEST_DIR)/test_cook_ether $(TEST_DIR)/test_cook_glider_A \
                   $(TEST_DIR)/test_cook_glider_E $(TEST_DIR)/test_cook_glider_F \
                   $(TEST_DIR)/test_cook_glider_G $(TEST_DIR)/test_cook_glider_H \
                   $(TEST_DIR)/test_cook_glider_gun \
                   $(TEST_DIR)/test_glider_phases $(TEST_DIR)/test_phase_verifier \
                   $(TEST_DIR)/test_phase_verifier_martinez \
                   $(TEST_DIR)/test_cook_collision_martinez \
                   $(TEST_DIR)/test_cook_ossifier \
                   $(TEST_DIR)/test_cook_data_block \
                   $(TEST_DIR)/test_hist $(TEST_DIR)/test_ext \
                   $(TEST_DIR)/test_sig $(TEST_DIR)/test_cont \
                   $(TEST_DIR)/test_bundle $(TEST_DIR)/test_unary \
                   $(TEST_DIR)/test_ask $(TEST_DIR)/test_external_binary \
                   $(TEST_DIR)/test_gap $(TEST_DIR)/test_package \
                   $(TEST_DIR)/test_name_cert $(TEST_DIR)/test_settled \
                   $(TEST_DIR)/test_topology_up $(TEST_DIR)/test_fold_up \
                   $(TEST_DIR)/test_circle_up \
                   $(TEST_DIR)/test_circle_up_audit \
                   $(TEST_DIR)/test_fold_up_audit \
                   $(TEST_DIR)/test_meta_cic_audit \
                   $(TEST_DIR)/test_topology_up_audit \
                   $(TEST_DIR)/test_r110_round_trip

.PHONY: all test test-r110 test-algo-r110 test-algo-r110-semantic test-algo-r110-idempotent test-algo-size-guard test-collision-audit test-exhaustiveness test-scale visualizations regen-manifests clean
all: $(STANDALONE_BINS) $(ENCODER_BINS)

# Generated manifests (.r110.ct, .algo.r110.ct) are encoder outputs — not in git.
# Pattern rules below regenerate them from source manifests (.enum.ct, .algo.ct)
# whenever the source or generator binary changes.
R110_GENERATED      := $(patsubst %.enum.ct,%.r110.ct,$(wildcard manifests/*/*.enum.ct))
ALGO_R110_GENERATED := $(patsubst %.algo.ct,%.algo.r110.ct,$(wildcard manifests/*/*.algo.ct))

manifests/%.r110.ct: manifests/%.enum.ct $(ENCODER_DIR)/generate_r110
	./$(ENCODER_DIR)/generate_r110 $< $@

manifests/%.algo.r110.ct: manifests/%.algo.ct $(ENCODER_DIR)/generate_r110_algo
	./$(ENCODER_DIR)/generate_r110_algo $< $@

regen-manifests: $(R110_GENERATED) $(ALGO_R110_GENERATED)

# Evaluators
$(EVAL_DIR)/rule110: $(EVAL_DIR)/rule110.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -DRULE110_STANDALONE_MAIN -o $@ $<

$(ENCODER_DIR)/generate_r110: $(ENCODER_DIR)/generate_r110.c
	$(CC) $(CFLAGS) -o $@ $<

$(ENCODER_DIR)/generate_r110_algo: $(ENCODER_DIR)/generate_r110_algo.c $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/cook_encode.h $(ENCODER_DIR)/block_assembler.h $(ENCODER_DIR)/block_assembler.c $(ENCODER_DIR)/cook_blocks.h $(ENCODER_DIR)/cook_blocks.c $(ENCODER_DIR)/cook_glider_D1.h $(ENCODER_DIR)/cook_glider_D1.c $(ENCODER_DIR)/cook_glider_D2.h $(ENCODER_DIR)/cook_glider_D2.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(ENCODER_DIR)/generate_r110_algo.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/cook_encode.c $(ENCODER_DIR)/cook_construction.c \
	    $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/block_assembler.c $(ENCODER_DIR)/cook_blocks.c \
	    $(ENCODER_DIR)/cook_glider_D1.c $(ENCODER_DIR)/cook_glider_D2.c

# Tests
$(TEST_DIR)/test_rule110: $(TEST_DIR)/test_rule110.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -o $@ $< $(EVAL_DIR)/rule110.c

$(TEST_DIR)/test_cyclic_tag: $(TEST_DIR)/test_cyclic_tag.c $(EVAL_DIR)/cyclic_tag.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -o $@ $< $(EVAL_DIR)/cyclic_tag.c

$(TEST_DIR)/test_encoder: $(TEST_DIR)/test_encoder.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ $< $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_cook_ether: $(TEST_DIR)/test_cook_ether.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_ether.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c

$(TEST_DIR)/test_cook_glider_A: $(TEST_DIR)/test_cook_glider_A.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_A.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c

$(TEST_DIR)/test_cook_glider_E: $(TEST_DIR)/test_cook_glider_E.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_E.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_E.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_E.c

$(TEST_DIR)/test_cook_glider_F: $(TEST_DIR)/test_cook_glider_F.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_F.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_F.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_F.c

$(TEST_DIR)/test_cook_glider_G: $(TEST_DIR)/test_cook_glider_G.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_G.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_G.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_G.c

$(TEST_DIR)/test_cook_glider_H: $(TEST_DIR)/test_cook_glider_H.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_H.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_H.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_H.c

$(TEST_DIR)/test_cook_glider_gun: $(TEST_DIR)/test_cook_glider_gun.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_gun.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_gun.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_gun.c

$(TEST_DIR)/test_glider_phases: $(TEST_DIR)/test_glider_phases.c $(ENCODER_DIR)/glider_phases.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_glider_phases.c \
	    $(ENCODER_DIR)/glider_phases.c

$(TEST_DIR)/test_phase_verifier: $(TEST_DIR)/test_phase_verifier.c $(ENCODER_DIR)/phase_verifier.c $(ENCODER_DIR)/phase_verifier.h $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/glider_phases.h $(EVAL_DIR)/rule110.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_phase_verifier.c \
	    $(ENCODER_DIR)/phase_verifier.c $(ENCODER_DIR)/glider_phases.c \
	    $(EVAL_DIR)/rule110.c

$(TEST_DIR)/test_phase_verifier_martinez: $(TEST_DIR)/test_phase_verifier_martinez.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/glider_phases.h $(EVAL_DIR)/rule110.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_phase_verifier_martinez.c \
	    $(ENCODER_DIR)/glider_phases.c $(EVAL_DIR)/rule110.c

$(TEST_DIR)/test_cook_collision_martinez: $(TEST_DIR)/test_cook_collision_martinez.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/glider_phases.h $(ENCODER_DIR)/cook_collisions.h $(ENCODER_DIR)/cook_collisions.c $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_detect.h $(ENCODER_DIR)/cook_detect.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_collision_martinez.c \
	    $(EVAL_DIR)/rule110.c $(ENCODER_DIR)/glider_phases.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_B.c \
	    $(ENCODER_DIR)/cook_glider_C.c $(ENCODER_DIR)/cook_glider_D.c \
	    $(ENCODER_DIR)/cook_collisions.c $(ENCODER_DIR)/cook_detect.c

$(TEST_DIR)/test_cook_ossifier: $(TEST_DIR)/test_cook_ossifier.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_ossifier.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_ossifier.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_ossifier.c

$(TEST_DIR)/test_cook_data_block: $(TEST_DIR)/test_cook_data_block.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_data_block.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_data_block.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_data_block.c

$(TEST_DIR)/test_mark: $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/cyclic_tag.h $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/cyclic_tag.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_hist: $(TEST_DIR)/test_hist.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_hist.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_ext: $(TEST_DIR)/test_ext.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_ext.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_sig: $(TEST_DIR)/test_sig.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_sig.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_cont: $(TEST_DIR)/test_cont.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_cont.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_bundle: $(TEST_DIR)/test_bundle.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_bundle.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_unary: $(TEST_DIR)/test_unary.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_unary.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_ask: $(TEST_DIR)/test_ask.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_ask.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_external_binary: $(TEST_DIR)/test_external_binary.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_external_binary.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_gap: $(TEST_DIR)/test_gap.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_gap.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_package: $(TEST_DIR)/test_package.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_package.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_name_cert: $(TEST_DIR)/test_name_cert.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_name_cert.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_settled: $(TEST_DIR)/test_settled.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_settled.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_topology_up: $(TEST_DIR)/test_topology_up.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_topology_up.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_fold_up: $(TEST_DIR)/test_fold_up.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_fold_up.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_circle_up: $(TEST_DIR)/test_circle_up.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_circle_up.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_circle_up_audit: $(TEST_DIR)/test_circle_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_circle_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_fold_up_audit: $(TEST_DIR)/test_fold_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_fold_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_meta_cic_audit: $(TEST_DIR)/test_meta_cic_audit.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_meta_cic_audit.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_topology_up_audit: $(TEST_DIR)/test_topology_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_topology_up_audit.c $(ENCODER_DIR)/groundcompiler_encoding.c

$(TEST_DIR)/test_r110_round_trip: $(TEST_DIR)/test_r110_round_trip.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_decode.h $(ENCODER_DIR)/block_assembler.h $(ENCODER_DIR)/block_assembler.c $(ENCODER_DIR)/cook_blocks.h $(ENCODER_DIR)/cook_blocks.c $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_construction.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_r110_round_trip.c \
	    $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_decode.c $(ENCODER_DIR)/glider_phases.c \
	    $(ENCODER_DIR)/cook_construction.c \
	    $(ENCODER_DIR)/block_assembler.c $(ENCODER_DIR)/cook_blocks.c

$(TOOLS_DIR)/manifest_exhaustiveness_audit: $(TOOLS_DIR)/manifest_exhaustiveness_audit.c $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(ENCODER_DIR) -o $@ \
	    $(TOOLS_DIR)/manifest_exhaustiveness_audit.c \
	    $(ENCODER_DIR)/groundcompiler_encoding.c

$(VISUALIZATION_TOOL): $(TOOLS_DIR)/visualize_rule110.c \
		$(EVAL_DIR)/rule110.c $(EVAL_DIR)/rule110.h \
		$(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/glider_phases.h \
		$(ENCODER_DIR)/cook_detect.c $(ENCODER_DIR)/cook_detect.h \
		$(ENCODER_DIR)/cook_encode.c $(ENCODER_DIR)/cook_encode.h \
		$(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_construction.h \
		$(ENCODER_DIR)/cook_leader.c $(ENCODER_DIR)/cook_leader.h \
		$(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_ossifier.h \
		$(ENCODER_DIR)/cook_data_block.c $(ENCODER_DIR)/cook_data_block.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TOOLS_DIR)/visualize_rule110.c \
	    $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_detect.c \
	    $(ENCODER_DIR)/cook_encode.c $(ENCODER_DIR)/cook_construction.c \
	    $(ENCODER_DIR)/cook_leader.c $(ENCODER_DIR)/cook_ossifier.c \
	    $(ENCODER_DIR)/cook_data_block.c

visualizations: $(VISUALIZATION_TOOL)
	mkdir -p ../docs/dossier/figures/rule110
	./$(VISUALIZATION_TOOL) ether > ../docs/dossier/figures/rule110/ether_evolution.svg
	./$(VISUALIZATION_TOOL) glider_zoo > ../docs/dossier/figures/rule110/glider_zoo.svg
	./$(VISUALIZATION_TOOL) collision > ../docs/dossier/figures/rule110/collision_example.svg
	./$(VISUALIZATION_TOOL) cook_packet > ../docs/dossier/figures/rule110/cook_packet_structure.svg
	./$(VISUALIZATION_TOOL) scale > ../docs/dossier/figures/rule110/scale_frontier.svg

test: $(TESTS) $(TOOLS) $(R110_GENERATED) $(ALGO_R110_GENERATED) test-algo-r110-semantic test-algo-r110-idempotent test-algo-size-guard
	@for t in $(TESTS); do \
	    echo "== $$t =="; \
	    ./$$t || exit 1; \
	done
	@echo "== $(TOOLS_DIR)/manifest_exhaustiveness_audit =="
	@./$(TOOLS_DIR)/manifest_exhaustiveness_audit
	@echo "ALL TESTS PASSED"

test-r110: $(TEST_DIR)/test_r110_round_trip
	./$(TEST_DIR)/test_r110_round_trip

test-algo-r110: $(TEST_DIR)/test_r110_round_trip
	./$(TEST_DIR)/test_r110_round_trip --algo

test-algo-r110-semantic: $(TEST_DIR)/test_r110_round_trip
	./$(TEST_DIR)/test_r110_round_trip --algo --semantic

test-algo-r110-idempotent: $(ENCODER_DIR)/generate_r110_algo
	./$(TEST_DIR)/test_algo_r110_idempotent.sh

test-algo-size-guard: $(ALGO_R110_GENERATED)
	./$(TEST_DIR)/test_algo_r110_size_guard.sh

test-collision-audit: $(TEST_DIR)/test_cook_collision_martinez
	./$(TEST_DIR)/test_cook_collision_martinez --strict

test-exhaustiveness: $(TOOLS_DIR)/manifest_exhaustiveness_audit
	./$(TOOLS_DIR)/manifest_exhaustiveness_audit --strict

clean:
	rm -f $(STANDALONE_BINS) $(ENCODER_BINS) $(TOOLS) $(VISUALIZATION_TOOL) $(TESTS) $(SCALE_TESTS)

TESTS += $(TEST_DIR)/test_cook_glider_B \
         $(TEST_DIR)/test_cook_glider_C \
         $(TEST_DIR)/test_cook_glider_D \
         $(TEST_DIR)/test_cook_glider_D1 \
         $(TEST_DIR)/test_cook_glider_D2 \
         $(TEST_DIR)/test_cook_collisions

test: $(TEST_DIR)/test_cook_glider_B \
      $(TEST_DIR)/test_cook_glider_C \
      $(TEST_DIR)/test_cook_glider_D \
      $(TEST_DIR)/test_cook_glider_D1 \
      $(TEST_DIR)/test_cook_glider_D2 \
      $(TEST_DIR)/test_cook_collisions

$(TEST_DIR)/test_cook_glider_B: $(TEST_DIR)/test_cook_glider_B.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_B.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_B.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_B.c

$(TEST_DIR)/test_cook_glider_C: $(TEST_DIR)/test_cook_glider_C.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_C.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_C.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_C.c

$(TEST_DIR)/test_cook_glider_D: $(TEST_DIR)/test_cook_glider_D.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_D.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_D.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_D.c

$(TEST_DIR)/test_cook_glider_D1: $(TEST_DIR)/test_cook_glider_D1.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/glider_phases.h $(ENCODER_DIR)/cook_glider_D1.h $(ENCODER_DIR)/cook_glider_D1.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_D1.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_D1.c

$(TEST_DIR)/test_cook_glider_D2: $(TEST_DIR)/test_cook_glider_D2.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/glider_phases.h $(ENCODER_DIR)/cook_glider_D2.h $(ENCODER_DIR)/cook_glider_D2.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_D2.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_D2.c

$(TEST_DIR)/test_cook_collisions: $(TEST_DIR)/test_cook_collisions.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_collisions.h $(ENCODER_DIR)/cook_glider_B.h $(ENCODER_DIR)/cook_glider_C.h $(ENCODER_DIR)/cook_glider_D.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_collisions.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_glider_B.c \
	    $(ENCODER_DIR)/cook_glider_C.c $(ENCODER_DIR)/cook_glider_D.c \
	    $(ENCODER_DIR)/cook_collisions.c

$(TEST_DIR)/test_cook_leader: $(TEST_DIR)/test_cook_leader.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_leader.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c

TESTS += $(TEST_DIR)/test_cook_leader
test: $(TEST_DIR)/test_cook_leader

$(TEST_DIR)/test_cook_encode_empty: $(TEST_DIR)/test_cook_encode_empty.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_encode_empty.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c

TESTS += $(TEST_DIR)/test_cook_encode_empty
test: $(TEST_DIR)/test_cook_encode_empty

$(TEST_DIR)/test_manifest_runner_r110: $(TEST_DIR)/test_manifest_runner_r110.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_manifest_runner_r110.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c

TESTS += $(TEST_DIR)/test_manifest_runner_r110
test: $(TEST_DIR)/test_manifest_runner_r110

$(TEST_DIR)/test_cook_encode_one: $(TEST_DIR)/test_cook_encode_one.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_encode_one.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c

TESTS += $(TEST_DIR)/test_cook_encode_one
test: $(TEST_DIR)/test_cook_encode_one

$(TEST_DIR)/test_cook_encode_arbitrary: $(TEST_DIR)/test_cook_encode_arbitrary.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_encode_arbitrary.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c

TESTS += $(TEST_DIR)/test_cook_encode_arbitrary
test: $(TEST_DIR)/test_cook_encode_arbitrary

$(TEST_DIR)/test_cook_packet_phase_exact: $(TEST_DIR)/test_cook_packet_phase_exact.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h $(ENCODER_DIR)/cook_decode.h $(ENCODER_DIR)/cook_decode.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_packet_phase_exact.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c $(ENCODER_DIR)/cook_decode.c

TESTS += $(TEST_DIR)/test_cook_packet_phase_exact
test: $(TEST_DIR)/test_cook_packet_phase_exact

$(TEST_DIR)/test_cook_packet_scale: $(TEST_DIR)/test_cook_packet_scale.c $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/cook_encode.h $(ENCODER_DIR)/cook_decode.h $(ENCODER_DIR)/cook_decode.c
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_packet_scale.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c \
	    $(ENCODER_DIR)/cook_leader.c $(ENCODER_DIR)/cook_ossifier.c \
	    $(ENCODER_DIR)/cook_data_block.c $(ENCODER_DIR)/cook_encode.c \
	    $(ENCODER_DIR)/cook_decode.c

SCALE_TESTS := $(TEST_DIR)/test_cook_packet_scale

test-scale: $(SCALE_TESTS)
	./$(TEST_DIR)/test_cook_packet_scale

$(TEST_DIR)/test_enum_cook_full_roundtrip: $(TEST_DIR)/test_enum_cook_full_roundtrip.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/cook_encode.h $(ENCODER_DIR)/cook_decode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_enum_cook_full_roundtrip.c \
	    $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c \
	    $(ENCODER_DIR)/cook_leader.c $(ENCODER_DIR)/cook_ossifier.c \
	    $(ENCODER_DIR)/cook_data_block.c $(ENCODER_DIR)/cook_encode.c \
	    $(ENCODER_DIR)/cook_decode.c

TESTS += $(TEST_DIR)/test_enum_cook_full_roundtrip
test: $(TEST_DIR)/test_enum_cook_full_roundtrip

$(TEST_DIR)/test_meta_cic: $(TEST_DIR)/test_meta_cic.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_meta_cic.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/groundcompiler_encoding.c

TESTS += $(TEST_DIR)/test_meta_cic
test: $(TEST_DIR)/test_meta_cic

$(TEST_DIR)/test_ground_compiler: $(TEST_DIR)/test_ground_compiler.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_ground_compiler.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/groundcompiler_encoding.c

TESTS += $(TEST_DIR)/test_ground_compiler
test: $(TEST_DIR)/test_ground_compiler

$(TEST_DIR)/test_external_baseline_martinez: $(TEST_DIR)/test_external_baseline_martinez.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -o $@ \
	    $(TEST_DIR)/test_external_baseline_martinez.c $(EVAL_DIR)/rule110.c

TESTS += $(TEST_DIR)/test_external_baseline_martinez
test: $(TEST_DIR)/test_external_baseline_martinez

$(TEST_DIR)/test_tm_end_to_end: $(TEST_DIR)/test_tm_end_to_end.c $(EVAL_DIR)/rule110.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/tm_to_tag.h $(ENCODER_DIR)/tag_to_cyclic.h $(ENCODER_DIR)/cook_encode.h $(ENCODER_DIR)/cook_decode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_tm_end_to_end.c \
	    $(EVAL_DIR)/rule110.c $(EVAL_DIR)/cyclic_tag.c \
	    $(ENCODER_DIR)/tm_to_tag.c $(ENCODER_DIR)/tag_to_cyclic.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/glider_phases.c \
	    $(ENCODER_DIR)/cook_leader.c $(ENCODER_DIR)/cook_ossifier.c \
	    $(ENCODER_DIR)/cook_data_block.c $(ENCODER_DIR)/cook_encode.c \
	    $(ENCODER_DIR)/cook_decode.c

TESTS += $(TEST_DIR)/test_tm_end_to_end
test: $(TEST_DIR)/test_tm_end_to_end
