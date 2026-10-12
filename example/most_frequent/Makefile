REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/most_frequent/rocq/mf_memory.vo example/most_frequent/rocq/most_frequent.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example most_frequent
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example most_frequent --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example most_frequent
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example most_frequent
report: docs test assemble
