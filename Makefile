SHELL := /bin/sh
UNAME_S := $(shell uname -s)
FLOW_DIR ?= ../FLOW
BUILD := build
LEAN ?= $(or $(shell command -v lean 2>/dev/null),$(HOME)/.elan/bin/lean)
LEANCHECKER ?= $(or $(shell command -v leanchecker 2>/dev/null),$(HOME)/.elan/bin/leanchecker)
AR ?= ar

ifeq ($(UNAME_S),Darwin)
LLVM_PREFIX ?= /opt/homebrew/opt/llvm/bin
LDFLAGS_STRIP := -Wl,-dead_strip
else
LLVM_PREFIX ?= /usr/bin
LDFLAGS_STRIP := -Wl,--gc-sections
endif
ifneq ($(wildcard $(LLVM_PREFIX)/clang),)
DEFAULT_CC := $(LLVM_PREFIX)/clang
DEFAULT_CXX := $(LLVM_PREFIX)/clang++
DEFAULT_FMT := $(LLVM_PREFIX)/clang-format
DEFAULT_TIDY := $(LLVM_PREFIX)/clang-tidy
else
DEFAULT_CC := clang
DEFAULT_CXX := clang++
DEFAULT_FMT := clang-format
DEFAULT_TIDY := clang-tidy
endif
ifeq ($(origin CC),default)
CC := $(DEFAULT_CC)
endif
ifeq ($(origin CXX),default)
CXX := $(DEFAULT_CXX)
endif
CLANG_FORMAT ?= $(DEFAULT_FMT)
CLANG_TIDY ?= $(DEFAULT_TIDY)

C17_RING0_FLAGS := -std=c17 -O2 -ffreestanding -nostdlib -fno-builtin -fno-stack-protector \
	-fno-jump-tables -mgeneral-regs-only -ffunction-sections -fdata-sections \
	-Wall -Wextra -Werror -Wpedantic -Wconversion -Wundef -Wmissing-prototypes
C17_HOST_FLAGS := -std=c17 -O2 -ffunction-sections -fdata-sections \
	-Wall -Wextra -Werror -Wpedantic -Wconversion -Wundef -Wmissing-prototypes
INC_RING0 := -Iinclude -I$(BUILD) -isystem $(FLOW_DIR)/core -isystem $(FLOW_DIR)/sdk
INC_HOST := -Iinclude -I$(BUILD) -isystem $(FLOW_DIR)/core -isystem $(FLOW_DIR)/sdk

C_SOURCES := include/info.h src/info_ring0.c src/info_decomp_main.c src/info_cert.h src/info_cli.c

.PHONY: all clean fmt verify-all verify experiments \
	gate0-lean-theory gate1-lean-schema gate2-ring0-audit gate3-selftest \
	gate4-cli-audit gate5-oracle gate6-sabotage gate7-format

all: $(BUILD)/libinfo.a $(BUILD)/info $(BUILD)/info_decomp

$(BUILD)/lean/Info/Coding.olean: Info/Coding.lean
	@mkdir -p $(dir $@)
	$(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info/Induction.olean: Info/Induction.lean
	@mkdir -p $(dir $@)
	$(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info/Bounds.olean: Info/Bounds.lean $(BUILD)/lean/Info/Coding.olean
	@mkdir -p $(dir $@)
	LEAN_PATH=$(BUILD)/lean $(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info/Causal.olean: Info/Causal.lean
	@mkdir -p $(dir $@)
	$(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info/ProofMDL.olean: Info/ProofMDL.lean $(BUILD)/lean/Info/Coding.olean
	@mkdir -p $(dir $@)
	LEAN_PATH=$(BUILD)/lean $(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info/Theory.olean: Info/Theory.lean \
		$(BUILD)/lean/Info/Coding.olean \
		$(BUILD)/lean/Info/Induction.olean \
		$(BUILD)/lean/Info/Bounds.olean \
		$(BUILD)/lean/Info/Causal.olean \
		$(BUILD)/lean/Info/ProofMDL.olean
	@mkdir -p $(dir $@)
	LEAN_PATH=$(BUILD)/lean $(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/lean/Info.olean: Info.lean
	@mkdir -p $(dir $@)
	LEAN_PATH=$(BUILD)/lean:$(FLOW_DIR)/build/lean $(LEAN) -DwarningAsError=true --root=. -o $@ $<

$(BUILD)/info_schema_abi.h: $(BUILD)/lean/Info.olean
	@mkdir -p $(BUILD)
	LEAN_PATH=$(BUILD)/lean:$(FLOW_DIR)/build/lean $(LEAN) --run Info.lean emit-schema $@

$(BUILD)/info_ring0.o: src/info_ring0.c include/info.h $(BUILD)/info_schema_abi.h
	@mkdir -p $(BUILD)
	$(CC) $(C17_RING0_FLAGS) $(INC_RING0) -c $< -o $@

$(BUILD)/libinfo.a: $(BUILD)/info_ring0.o
	$(AR) rcs $@ $<

$(BUILD)/info_decomp: $(BUILD)/info_ring0.o src/info_decomp_main.c include/info.h $(BUILD)/info_schema_abi.h
	$(CC) $(C17_HOST_FLAGS) $(INC_HOST) $(LDFLAGS_STRIP) $(BUILD)/info_ring0.o src/info_decomp_main.c -o $@

$(BUILD)/info: $(BUILD)/info_ring0.o src/info_cli.c src/info_cert.h include/info.h $(BUILD)/info_schema_abi.h
	$(CC) $(C17_HOST_FLAGS) $(INC_HOST) $(LDFLAGS_STRIP) $(BUILD)/info_ring0.o src/info_cli.c -o $@

gate0-lean-theory: $(BUILD)/lean/Info/Theory.olean
	@echo "[Gate 0] Checking 5 pure-theory pillars via leanchecker and axiom audit..."
	@if grep -qiE '\bsorry\b' Info/Coding.lean Info/Induction.lean Info/Bounds.lean Info/Causal.lean Info/ProofMDL.lean Info/Theory.lean; then \
		echo "ERROR: sorry found in Info theory modules"; exit 1; \
	fi
	@for m in Info.Coding Info.Induction Info.Bounds Info.Causal Info.ProofMDL Info.Theory; do \
		LEAN_PATH=$(BUILD)/lean $(LEANCHECKER) $$m || exit 1; \
	done
	@python3 -c 'import pathlib, re; mods=[("Info.Coding","Info/Coding.lean"),("Info.Induction","Info/Induction.lean"),("Info.Bounds","Info/Bounds.lean"),("Info.Causal","Info/Causal.lean"),("Info.ProofMDL","Info/ProofMDL.lean")]; thms=[f"#print axioms {m}.{n}" for m,p in mods for n in re.findall(r"^theorem\s+(\S+)", pathlib.Path(p).read_text(encoding="utf-8"), re.M)]; assert len(thms)==94, f"Expected 94 theorems, got {len(thms)}"; pathlib.Path("$(BUILD)/info_axioms.in").write_text("import Info.Theory\n" + "\n".join(thms) + "\n", encoding="utf-8")'
	@LEAN_PATH=$(BUILD)/lean $(LEAN) --stdin < $(BUILD)/info_axioms.in > $(BUILD)/info_axioms.txt
	@if grep -q 'sorryAx' $(BUILD)/info_axioms.txt; then echo "ERROR: sorryAx detected"; exit 1; fi
	@if grep -q 'Lean\.ofReduceBool' $(BUILD)/info_axioms.txt; then echo "ERROR: Lean.ofReduceBool detected"; exit 1; fi
	@echo "[Gate 0] PASS (Info.Theory 94 theorems, 0 sorryAx, 0 ofReduceBool)"

gate1-lean-schema: $(BUILD)/info_schema_abi.h
	@echo "[Gate 1] Auditing Info.lean pure schema config and generated ABI header..."
	@if grep -qE '^\s*(theorem|lemma|axiom)\s' Info.lean; then \
		echo "ERROR: theorems/lemmas/axioms not allowed in Info.lean"; exit 1; \
	fi
	@rm -rf $(BUILD)/lean_schema_check && mkdir -p $(BUILD)/lean_schema_check && cp $(BUILD)/lean/Info.olean $(BUILD)/lean_schema_check/Info.olean
	LEAN_PATH=$(BUILD)/lean_schema_check:$(FLOW_DIR)/build/lean $(LEANCHECKER) Info
	@rm -rf $(BUILD)/lean_schema_check
	@if grep -q 'memcpy' $(BUILD)/info_schema_abi.h; then \
		echo "ERROR: memcpy found in generated ABI header"; exit 1; \
	fi
	@echo "[Gate 1] PASS (256-slot ABI 0 memcpy, leanchecker Info PASS)"

gate2-ring0-audit: $(BUILD)/info_ring0.o $(BUILD)/libinfo.a
	@echo "[Gate 2] Auditing Ring-0 freestanding Pure-GPR object..."
	@test -z "$$(nm -u $(BUILD)/info_ring0.o)"
ifeq ($(UNAME_S),Darwin)
	@if otool -tV $(BUILD)/info_ring0.o | grep -qE '\b(udiv|sdiv|fdiv|fmul|fadd|fsub|blr|br)\b|v[0-9]+\.'; then \
		echo "ERROR: Forbidden instruction or vector register in info_ring0.o"; exit 1; \
	fi
else
	@if objdump -d $(BUILD)/info_ring0.o | grep -qE '\b(udiv|sdiv|fdiv|fmul|fadd|fsub|blr|br)\b|%?[xyz]mm[0-9]+|\bv[0-9]+\.'; then \
		echo "ERROR: Forbidden instruction or vector register in info_ring0.o"; exit 1; \
	fi
endif
	@echo '#include "info.h"' | $(CXX) -std=c++20 -x c++ -fsyntax-only -Wall -Wextra -Werror $(INC_RING0) -
	$(CLANG_TIDY) --header-filter='info\.h$$' --checks='clang-analyzer-*,bugprone-*,-bugprone-easily-swappable-parameters' \
		--warnings-as-errors='*' src/info_ring0.c -- -std=c17 $(INC_RING0)
	@echo "[Gate 2] PASS (0 undef symbols, Pure-GPR clean, C++20 clean, clang-tidy 0 warnings)"

gate3-selftest: $(BUILD)/info
	@echo "[Gate 3] Running built-in 18-suite Ring-0 + cert selftest..."
	./$(BUILD)/info selftest
	@echo "[Gate 3] PASS"

gate4-cli-audit: $(BUILD)/info $(BUILD)/info_decomp
	@echo "[Gate 4] Auditing CLI & standalone decomp linkage (0 leanshared, 0 heap allocators)..."
	@for bin in $(BUILD)/info $(BUILD)/info_decomp; do \
		if [ "$(UNAME_S)" = "Darwin" ]; then \
			if otool -L $$bin | grep -qi 'leanshared'; then echo "ERROR: leanshared linked in $$bin"; exit 1; fi; \
		else \
			if ldd $$bin | grep -qi 'leanshared'; then echo "ERROR: leanshared linked in $$bin"; exit 1; fi; \
		fi; \
		if nm -u $$bin | grep -qE '[[:space:]]_?(malloc|free|calloc|realloc)([[:space:]@]|$$)'; then \
			echo "ERROR: heap allocator symbol linked in $$bin"; exit 1; \
		fi; \
	done
	@echo "[Gate 4] PASS (info + info_decomp clean, decomp size=$$(wc -c < $(BUILD)/info_decomp | tr -d ' ') B)"

gate5-oracle: gate0-lean-theory gate1-lean-schema gate4-cli-audit
	@echo "[Gate 5] Running independent pure-Python exact oracle + live Lean replay..."
	python3 oracles/verify_info_oracle.py
	@echo "[Gate 5] PASS"

gate6-sabotage: gate1-lean-schema
	@echo "[Gate 6] Running 42-mutant single-fault sabotage gate..."
	python3 tools/info_sabotage_check.py
	@echo "[Gate 6] PASS"

gate7-format:
	@echo "[Gate 7] Verifying clang-format compliance..."
	$(CLANG_FORMAT) --dry-run --Werror $(C_SOURCES)
	@echo "[Gate 7] PASS"

experiments: $(BUILD)/info $(BUILD)/info_decomp $(BUILD)/lean/Info/Theory.olean
	@echo "[Experiments] Running 7 compression, intelligence, CTW, Delsarte LP, Ecosystem, Lean Proof MDL & .infp Codec suites..."
	python3 experiments/hutter_benchmark.py
	python3 experiments/intelligence_downstream.py
	python3 experiments/ctw_switching_atlas.py
	python3 experiments/delsarte_coding_atlas.py
	python3 experiments/ecosystem_mdl_audit.py
	python3 experiments/lean_proof_distill.py
	python3 experiments/infp_proof_codec_benchmark.py
	@echo "[Experiments] PASS"

verify-all: gate0-lean-theory gate1-lean-schema gate2-ring0-audit gate3-selftest \
	gate4-cli-audit gate5-oracle gate6-sabotage gate7-format
	@echo "================================================================"
	@echo "INFO v1.0.0 — ALL 8 VERIFICATION GATES PASSED"
	@echo "================================================================"

verify: verify-all

fmt:
	$(CLANG_FORMAT) -i $(C_SOURCES)

clean:
	rm -rf $(BUILD)
