REPO := ../..
PYTHON ?= python3
EXPLANATIONS ?= auto
.PHONY: build extract test verify readable
build:
	$(MAKE) -C $(REPO) example/authenticator/rocq/model.vo example/authenticator/rocq/program.vo example/authenticator/rocq/base32.vo example/authenticator/rocq/accounts.vo example/authenticator/rocq/refinement.vo example/authenticator/rocq/extract.vo
extract: build
	$(PYTHON) scripts/check.py --extract-only
test: build
	$(PYTHON) scripts/check.py
verify:
	$(MAKE) -C $(REPO) verify
readable:
	cd $(REPO) && $(PYTHON) -m tools.rocq_readable build --sources example/authenticator/rocq --output example/authenticator/docs/rocq --explanations $(EXPLANATIONS)
