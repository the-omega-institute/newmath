# rule110 — BEDC ground-up minimal-trust vertical slice
# zero external deps, ANSI C99

CC      ?= cc
CFLAGS  ?= -std=c99 -O2 -Wall -Wextra -Wpedantic -Wshadow -Wno-unused-parameter
LDFLAGS ?=

EVAL_DIR    := evaluator
ENCODER_DIR := encoder
TEST_DIR    := tests

# Only rule110 evaluator ships as a standalone binary (with STANDALONE_MAIN).
# cyclic_tag and groundcompiler_encoding are libraries compiled into test binaries.
STANDALONE_BINS := $(EVAL_DIR)/rule110
TESTS           := $(TEST_DIR)/test_rule110 $(TEST_DIR)/test_cyclic_tag \
                   $(TEST_DIR)/test_encoder $(TEST_DIR)/test_mark \
                   $(TEST_DIR)/test_cook_ether $(TEST_DIR)/test_cook_glider_A \
                   $(TEST_DIR)/test_cook_glider_E $(TEST_DIR)/test_cook_glider_F \
                   $(TEST_DIR)/test_cook_glider_G $(TEST_DIR)/test_cook_glider_H \
                   $(TEST_DIR)/test_cook_glider_gun \
                   $(TEST_DIR)/test_cook_ossifier \
                   $(TEST_DIR)/test_cook_data_block

.PHONY: all test clean
all: $(STANDALONE_BINS)

# Evaluators
$(EVAL_DIR)/rule110: $(EVAL_DIR)/rule110.c $(EVAL_DIR)/rule110.h
	$(CC) $(CFLAGS) -DRULE110_STANDALONE_MAIN -o $@ $<

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
	    $(ENCODER_DIR)/cook_construction.c

$(TEST_DIR)/test_cook_glider_A: $(TEST_DIR)/test_cook_glider_A.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_A.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c

$(TEST_DIR)/test_cook_glider_E: $(TEST_DIR)/test_cook_glider_E.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_E.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_E.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_E.c

$(TEST_DIR)/test_cook_glider_F: $(TEST_DIR)/test_cook_glider_F.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_F.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_F.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_F.c

$(TEST_DIR)/test_cook_glider_G: $(TEST_DIR)/test_cook_glider_G.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_G.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_G.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_G.c

$(TEST_DIR)/test_cook_glider_H: $(TEST_DIR)/test_cook_glider_H.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_H.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_H.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_H.c

$(TEST_DIR)/test_cook_glider_gun: $(TEST_DIR)/test_cook_glider_gun.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_gun.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_gun.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_gun.c

$(TEST_DIR)/test_cook_ossifier: $(TEST_DIR)/test_cook_ossifier.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_ossifier.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_ossifier.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_ossifier.c

$(TEST_DIR)/test_cook_data_block: $(TEST_DIR)/test_cook_data_block.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_data_block.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_data_block.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_data_block.c

$(TEST_DIR)/test_mark: $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/cyclic_tag.h $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/cyclic_tag.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/groundcompiler_encoding.c

test: $(TESTS)
	@for t in $(TESTS); do \
	    echo "== $$t =="; \
	    ./$$t || exit 1; \
	done
	@echo "ALL TESTS PASSED"

clean:
	rm -f $(STANDALONE_BINS) $(TESTS)

TESTS += $(TEST_DIR)/test_cook_glider_B \
         $(TEST_DIR)/test_cook_glider_C \
         $(TEST_DIR)/test_cook_glider_D \
         $(TEST_DIR)/test_cook_collisions

test: $(TEST_DIR)/test_cook_glider_B \
      $(TEST_DIR)/test_cook_glider_C \
      $(TEST_DIR)/test_cook_glider_D \
      $(TEST_DIR)/test_cook_collisions

$(TEST_DIR)/test_cook_glider_B: $(TEST_DIR)/test_cook_glider_B.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_B.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_B.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_B.c

$(TEST_DIR)/test_cook_glider_C: $(TEST_DIR)/test_cook_glider_C.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_C.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_C.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_C.c

$(TEST_DIR)/test_cook_glider_D: $(TEST_DIR)/test_cook_glider_D.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_glider_D.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_glider_D.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_D.c

$(TEST_DIR)/test_cook_collisions: $(TEST_DIR)/test_cook_collisions.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_collisions.h $(ENCODER_DIR)/cook_glider_B.h $(ENCODER_DIR)/cook_glider_C.h $(ENCODER_DIR)/cook_glider_D.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_collisions.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_glider_B.c \
	    $(ENCODER_DIR)/cook_glider_C.c $(ENCODER_DIR)/cook_glider_D.c \
	    $(ENCODER_DIR)/cook_collisions.c

$(TEST_DIR)/test_cook_leader: $(TEST_DIR)/test_cook_leader.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_leader.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_leader.c

TESTS += $(TEST_DIR)/test_cook_leader
test: $(TEST_DIR)/test_cook_leader

$(TEST_DIR)/test_cook_encode_empty: $(TEST_DIR)/test_cook_encode_empty.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_encode_empty.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_leader.c \
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
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c

TESTS += $(TEST_DIR)/test_cook_encode_one
test: $(TEST_DIR)/test_cook_encode_one

$(TEST_DIR)/test_cook_encode_arbitrary: $(TEST_DIR)/test_cook_encode_arbitrary.c $(EVAL_DIR)/rule110.h $(ENCODER_DIR)/cook_construction.h $(ENCODER_DIR)/cook_leader.h $(ENCODER_DIR)/cook_ossifier.h $(ENCODER_DIR)/cook_data_block.h $(ENCODER_DIR)/cook_encode.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -o $@ \
	    $(TEST_DIR)/test_cook_encode_arbitrary.c $(EVAL_DIR)/rule110.c \
	    $(ENCODER_DIR)/cook_construction.c $(ENCODER_DIR)/cook_leader.c \
	    $(ENCODER_DIR)/cook_ossifier.c $(ENCODER_DIR)/cook_data_block.c \
	    $(ENCODER_DIR)/cook_encode.c

TESTS += $(TEST_DIR)/test_cook_encode_arbitrary
test: $(TEST_DIR)/test_cook_encode_arbitrary
