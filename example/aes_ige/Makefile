REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/aes_ige/rocq/ige.vo example/aes_ige/rocq/extract.vo
verify:
	$(MAKE) -C $(REPO) verify
	$(PYTHON) scripts/verification.py
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example aes_ige
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example aes_ige --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example aes_ige
assemble:
	$(PYTHON) scripts/report.py
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example aes_ige
report: docs test assemble
