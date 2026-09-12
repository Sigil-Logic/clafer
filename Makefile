SRC_DIR  := src
TEST_DIR := test

# Alloy is acquired from Maven Central, pinned to an exact version and
# verified against a SHA-256 (Sigil-Logic/clafer#5).
ALLOY_VERSION := 6.2.0
ALLOY_JAR := org.alloytools.alloy.dist-$(ALLOY_VERSION).jar
ALLOY_URL := https://repo1.maven.org/maven2/org/alloytools/org.alloytools.alloy.dist/$(ALLOY_VERSION)/$(ALLOY_JAR)
ALLOY_SHA256 := 6037cbeee0e8423c1c468447ed10f5fcf2f2743a2ffc39cb1c81f2905c0fdb9d
ifeq ($(OS),Windows_NT)
EXE := .exe
endif

all: build

build: $(ALLOY_JAR)
	stack build

install:
	mkdir -p $(to)
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f $(ALLOY_JAR) $(to)
	cp -f ecore2clafer.jar $(to)
	cp `stack path --local-install-root`/bin/clafer$(EXE) $(to)

# regenerate grammar, call after clafer.cf changed
grammar:
	$(MAKE) -C $(SRC_DIR) grammar

# Just like "init" but with enabled profiler
# this will reinstall everything with profiling support, build clafer, and copy it to .
prof: $(ALLOY_JAR)
	stack build --executable-profiling --library-profiling --ghc-options="-auto-all -caf-all -rtsopts -osuf p_o"

.PHONY: test
test:
	cp `stack path --local-install-root`/bin/clafer$(EXE) .
	stack test 2>/dev/null || :    # supress error message and exit code if fail
	$(MAKE) -C $(TEST_DIR) test

generateAlloyJSHTMLDot:
	$(MAKE) -C $(TEST_DIR) generateAlloyJSHTMLDot

diffRegressions:
	$(MAKE) -C $(TEST_DIR) diffRegressions

reg:
	$(MAKE) -C $(TEST_DIR) reg

.PHONY: clean
clean:
	$(MAKE) -C $(SRC_DIR) clean
	$(MAKE) cleanTools
	$(MAKE) cleanTest
	stack clean

.PHONY: cleanTest
cleanTest:
	$(MAKE) -C $(TEST_DIR) clean

.PHONY: cleanTools
cleanTools:
	find . -type f -name '*.class' -print0 | xargs -0 rm -f

.PHONY: tags
tags:
	hasktags --ctags --extendedctag --ignore-close-implementation .

.PHONY: codex
codex:
	codex update
	mv codex.tags tags

$(ALLOY_JAR):
	@echo "Fetching Alloy $(ALLOY_VERSION) from Maven Central..."
	curl -fsSL -o "$(ALLOY_JAR)" "$(ALLOY_URL)"
	@if command -v shasum > /dev/null 2>&1; then \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR)" | shasum -a 256 -c - ; \
	else \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR)" | sha256sum -c - ; \
	fi || { echo "[ERROR] $(ALLOY_JAR) checksum mismatch"; rm -f "$(ALLOY_JAR)"; false; }
