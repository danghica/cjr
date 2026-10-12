REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/list_rev/rocq/list_rev.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example list_rev
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example list_rev --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example list_rev
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example list_rev
report: docs test assemble
