REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build extract test verify proofs readable cli ui frontends frontend-test run-cli run-ui docs-check
CORE_OBJECTS := $(patsubst %.v,%.vo,$(wildcard core/rocq/*.v))
build:
	$(MAKE) -C $(REPO) $(addprefix example/authenticator/,$(CORE_OBJECTS))
extract: build
	$(PYTHON) core/scripts/check.py --extract-only
test: build
	$(PYTHON) core/scripts/check.py
proofs: build
	$(PYTHON) core/scripts/verify.py
verify:
	$(MAKE) -C $(REPO) verify
readable: build
	cd $(REPO) && $(PYTHON) -m tools.rocq_readable build --sources example/authenticator/core/rocq --output example/authenticator/docs/rocq --explanations $(EXPLANATIONS)

# Frontend builds enforce a current passed core proof/runtime report.
cli:
	$(PYTHON) scripts/frontends.py cli
ui:
	$(PYTHON) scripts/frontends.py ui
frontends: cli ui
frontend-test:
	$(PYTHON) scripts/check_frontends.py
run-cli: cli
	build/frontend/authenticator
run-ui: ui
	open build/frontend/Authenticator.app

docs-check:
	$(PYTHON) scripts/check_docs.py
