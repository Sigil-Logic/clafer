SRC_DIR  := src
TEST_DIR := test

# Alloy is acquired from Maven Central, pinned to an exact version and
# verified against a SHA-256 (Sigil-Logic/clafer#5).
ALLOY_VERSION := 6.2.0
ALLOY_JAR := org.alloytools.alloy.dist-$(ALLOY_VERSION).jar
ALLOY_URL := https://repo1.maven.org/maven2/org/alloytools/org.alloytools.alloy.dist/$(ALLOY_VERSION)/$(ALLOY_JAR)
ALLOY_SHA256 := 6037cbeee0e8423c1c468447ed10f5fcf2f2743a2ffc39cb1c81f2905c0fdb9d

# chocosolver is built from the Sigil-Logic fork at a pinned commit
# (Sigil-Logic/clafer#13).  No upstream binary exists to pin: the only
# gsdlab/chocosolver release (0.3.5, 2014) carries no jar assets and
# org.clafer:chocosolver was never published to Maven Central.  Integrity
# comes from the content-addressed pinned commit plus Maven's checksum
# verification of the resolved dependencies; building from source mirrors
# the alloyIG.jar decision from Sigil-Logic/clafer#5.
CHOCOSOLVER_REPO := https://github.com/Sigil-Logic/chocosolver.git
CHOCOSOLVER_COMMIT := bc4cb12a23118d9e5d7f1003d83f2f8bed9cf179
CHOCOSOLVER_VERSION := 0.4.4
CHOCOSOLVER_JAR := chocosolver.jar
CHOCOSOLVER_BUILD_DIR := chocosolver-build.tmp
ifeq ($(OS),Windows_NT)
EXE := .exe
endif

all: build

build: $(ALLOY_JAR)
	$(MAKE) verify-alloy
	stack build

install: build verify-chocosolver
	mkdir -p $(to)
	cp -f README.md $(to)/clafer-README.md
	cp -f LICENSE $(to)/
	cp -f CHANGES.md $(to)/clafer-CHANGES.md
	cp -f $(ALLOY_JAR) $(to)
	cp -f $(CHOCOSOLVER_JAR) $(to)
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
test: build verify-chocosolver
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

# Download to a temporary file, verify, then atomically rename, so an
# interrupted or corrupted download never becomes an "up to date" target.
$(ALLOY_JAR):
	@echo "Fetching Alloy $(ALLOY_VERSION) from Maven Central..."
	curl -fsSL -o "$(ALLOY_JAR).tmp" "$(ALLOY_URL)"
	@if command -v shasum > /dev/null 2>&1; then \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR).tmp" | shasum -a 256 -c - ; \
	else \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR).tmp" | sha256sum -c - ; \
	fi || { echo "[ERROR] $(ALLOY_JAR) checksum mismatch"; rm -f "$(ALLOY_JAR).tmp"; false; }
	mv "$(ALLOY_JAR).tmp" "$(ALLOY_JAR)"

# Clone the fork at the pinned commit (--no-checkout so the unpinned
# default branch is never materialized), verify HEAD matches the pin,
# build with Maven, then atomically rename the staged jar.  The recipe is
# one fail-fast shell block whose EXIT trap removes the build directory
# and staging file on any outcome, so an interrupted or wrong-revision
# build never becomes an "up to date" target and leaves no residue.
# Tests are the fork's own CI's responsibility (Sigil-Logic/chocosolver);
# this target only acquires the artifact, hence -DskipTests.  The sidecar
# $(CHOCOSOLVER_JAR).commit stamp records the pin the jar was built from,
# for verify-chocosolver below.
$(CHOCOSOLVER_JAR):
	@echo "Building chocosolver $(CHOCOSOLVER_VERSION) from $(CHOCOSOLVER_REPO) @ $(CHOCOSOLVER_COMMIT)..."
	set -e; \
	trap 'rm -rf "$(CHOCOSOLVER_BUILD_DIR)" "$(CHOCOSOLVER_JAR).tmp"' EXIT; \
	rm -rf "$(CHOCOSOLVER_BUILD_DIR)" "$(CHOCOSOLVER_JAR).tmp"; \
	git clone -q --filter=blob:none --no-checkout "$(CHOCOSOLVER_REPO)" "$(CHOCOSOLVER_BUILD_DIR)"; \
	git -C "$(CHOCOSOLVER_BUILD_DIR)" checkout -q "$(CHOCOSOLVER_COMMIT)"; \
	actual=$$(git -C "$(CHOCOSOLVER_BUILD_DIR)" rev-parse HEAD); \
	test "$$actual" = "$(CHOCOSOLVER_COMMIT)" || { echo "[ERROR] chocosolver checkout is $$actual, not the pinned commit $(CHOCOSOLVER_COMMIT)"; exit 1; }; \
	mvn -q -f "$(CHOCOSOLVER_BUILD_DIR)/pom.xml" -DskipTests package; \
	cp "$(CHOCOSOLVER_BUILD_DIR)/target/chocosolver-$(CHOCOSOLVER_VERSION)-jar-with-dependencies.jar" "$(CHOCOSOLVER_JAR).tmp"; \
	mv "$(CHOCOSOLVER_JAR).tmp" "$(CHOCOSOLVER_JAR)"; \
	printf '%s\n' "$(CHOCOSOLVER_COMMIT)" > "$(CHOCOSOLVER_JAR).commit"

# Re-verify the pin stamp on every test/install entry, so a jar left from
# before a pin bump (or an unrelated file at that path) is caught even
# though make considers the file target up to date.  Mirrors verify-alloy.
.PHONY: verify-chocosolver
verify-chocosolver: $(CHOCOSOLVER_JAR)
	@test -f "$(CHOCOSOLVER_JAR).commit" && \
	test "$$(cat "$(CHOCOSOLVER_JAR).commit")" = "$(CHOCOSOLVER_COMMIT)" \
		|| { echo "[ERROR] $(CHOCOSOLVER_JAR) does not match the pinned commit $(CHOCOSOLVER_COMMIT); delete $(CHOCOSOLVER_JAR) and $(CHOCOSOLVER_JAR).commit and re-run make"; false; }

# Re-verify the jar on every build entry, so a pre-existing corrupt file is
# caught even though make considers the target up to date.
.PHONY: verify-alloy
verify-alloy:
	@if command -v shasum > /dev/null 2>&1; then \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR)" | shasum -a 256 -c - ; \
	else \
		echo "$(ALLOY_SHA256)  $(ALLOY_JAR)" | sha256sum -c - ; \
	fi || { echo "[ERROR] $(ALLOY_JAR) failed verification; delete it and re-run make"; false; }
