REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/qsort/rocq/qsort.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example qsort
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example qsort --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example qsort
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example qsort
report: docs test assemble
