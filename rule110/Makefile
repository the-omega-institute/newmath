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
                   $(TEST_DIR)/test_cook_ether $(TEST_DIR)/test_cook_glider_A

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

$(TEST_DIR)/test_mark: $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c $(TEST_DIR)/manifest_runner.h $(EVAL_DIR)/cyclic_tag.h $(ENCODER_DIR)/groundcompiler_encoding.h
	$(CC) $(CFLAGS) -I$(EVAL_DIR) -I$(ENCODER_DIR) -I$(TEST_DIR) -o $@ \
	    $(TEST_DIR)/test_mark.c $(TEST_DIR)/manifest_runner.c \
	    $(EVAL_DIR)/cyclic_tag.c $(ENCODER_DIR)/groundcompiler_encoding.c

test: $(TESTS)
	@for t in $(TESTS); do \
	    echo "== $$t =="; \
	    ./$$t || exit 1; \
	done
	@echo "ALL TESTS PASSED"

clean:
	rm -f $(STANDALONE_BINS) $(TESTS)
