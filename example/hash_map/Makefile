REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/hash_map/rocq/hm_tactics.vo example/hash_map/rocq/hash_map.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example hash_map
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example hash_map --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example hash_map
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example hash_map
report: docs test assemble
