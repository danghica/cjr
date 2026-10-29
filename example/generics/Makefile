REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/generics/rocq/generic_examples.vo example/generics/rocq/generic_tests.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	$(MAKE) -C $(REPO) generic-extraction-test
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example generics
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example generics --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example generics
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example generics
report: docs test assemble
