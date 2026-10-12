REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build verify extract test docs benchmark report assemble
build:
	$(MAKE) -C $(REPO) example/misc/rocq/arith.vo example/misc/rocq/struct_upd.vo example/misc/rocq/cell.vo example/misc/rocq/swap.vo example/misc/rocq/sum_block.vo example/misc/rocq/class_upd.vo example/misc/rocq/frame_call.vo example/misc/rocq/vtable.vo
verify:
	$(MAKE) -C $(REPO) verify
extract:
	$(MAKE) -C $(REPO) extract
test: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples test --example misc
docs: build
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples readable --example misc --explanations $(EXPLANATIONS)
benchmark: extract
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples benchmark --example misc
assemble:
	cd $(REPO) && $(PYTHON) -m tools.project_tools.examples report --example misc
report: docs test assemble
