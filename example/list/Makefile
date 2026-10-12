REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/list/rocq/list.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example list
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example list --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example list
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example list
report: docs test assemble
