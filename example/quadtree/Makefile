PYTHON ?= python3
EXPLANATIONS ?= auto
COQC ?= $(HOME)/.opam/default/bin/coqc
COQCHK ?= $(HOME)/.opam/default/bin/coqchk
COQFLAGS = -R ../../theories cjr -Q . cjr.quadtree -Q ../../tools/extraction/rocq cjr.examples -Q ../array_list/rocq cjr.examples -Q ../array/rocq cjr.examples -Q ../hash_map/rocq cjr.examples -w +admitted-proof
SOURCES = spec/model.v spec/bounds.v algorithm/program.v proof/ownership.v proof/routing.v proof/helpers.v proof/correctness.v proof/insertion_model.v proof/insertion_helpers.v proof/insertion.v proof/algebra.v algorithm/extract.v
OBJECTS = $(SOURCES:.v=.vo)
.PHONY: build shared verify extract test benchmark docs report assemble
shared:
	$(MAKE) -C ../.. tools/extraction/rocq/cj_print.vo example/hash_map/rocq/hm_tactics.vo
$(OBJECTS): | shared
build: $(OBJECTS)
spec/model.vo: spec/model.v
	$(COQC) $(COQFLAGS) $<
algorithm/program.vo: algorithm/program.v
	$(COQC) $(COQFLAGS) $<
proof/ownership.vo: proof/ownership.v spec/model.vo
	$(COQC) $(COQFLAGS) $<
proof/routing.vo: proof/routing.v spec/model.vo
	$(COQC) $(COQFLAGS) $<
proof/helpers.vo: proof/helpers.v proof/ownership.vo proof/routing.vo algorithm/program.vo
	$(COQC) $(COQFLAGS) $<
proof/correctness.vo: proof/correctness.v proof/helpers.vo
	$(COQC) $(COQFLAGS) $<
algorithm/extract.vo: algorithm/extract.v algorithm/program.vo
	$(COQC) $(COQFLAGS) $<
verify: build
	COQC=$(COQC) COQCHK=$(COQCHK) $(PYTHON) scripts/verify.py
extract: build
	COQC=$(COQC) $(PYTHON) scripts/extract.py
test: extract
	$(PYTHON) scripts/test.py
benchmark: extract
	$(PYTHON) ../../tools/project_tools/benchmark.py run benchmark/benchmark.config.json
	$(PYTHON) ../../tools/project_tools/benchmark.py plot benchmark/benchmark.config.json
	$(PYTHON) ../../tools/project_tools/benchmark.py report benchmark/benchmark.config.json
docs: build
	PATH="$(HOME)/.opam/default/bin:$$PATH" ../../rocq-readable build --output docs/rocq --timeout 600 --explanations $(EXPLANATIONS)
	$(PYTHON) ../../tools/project_tools/docs.py metadata project.config.json
report:
	$(MAKE) verify
	$(MAKE) extract
	$(MAKE) docs
	$(MAKE) test
	$(MAKE) benchmark
	$(MAKE) assemble
assemble:
	$(PYTHON) ../../tools/project_tools/docs.py test-report project.config.json
	$(PYTHON) ../../tools/project_tools/docs.py report project.config.json

spec/bounds.vo: spec/bounds.v spec/model.vo
	$(COQC) $(COQFLAGS) $<
proof/insertion_model.vo: proof/insertion_model.v proof/routing.vo
	$(COQC) $(COQFLAGS) $<
proof/insertion_helpers.vo: proof/insertion_helpers.v proof/insertion_model.vo proof/helpers.vo
	$(COQC) $(COQFLAGS) $<
proof/insertion.vo: proof/insertion.v proof/insertion_helpers.vo
	$(COQC) $(COQFLAGS) $<

proof/algebra.vo: proof/algebra.v proof/correctness.vo proof/insertion.vo
	$(COQC) $(COQFLAGS) $<
