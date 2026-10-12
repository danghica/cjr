REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/array_list/rocq/array_list.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example array_list
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example array_list --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example array_list
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example array_list
report: docs test assemble
