REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/array/rocq/array.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example array
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example array --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example array
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example array
report: docs test assemble
