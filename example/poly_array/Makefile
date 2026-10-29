REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/poly_array/rocq/poly_array.vo example/poly_array/rocq/poly_array_tests.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	$(MAKE) -C $(REPO) generic-extraction-test
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example poly_array
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example poly_array --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example poly_array
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example poly_array
report: docs test assemble
