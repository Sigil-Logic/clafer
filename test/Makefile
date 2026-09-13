SUITE_DIR = positive
REG_DIR = regression
# -v stays in the generation flags for OUTPUT PARITY, not for its
# advisory validation: the Alloy generator suppresses the 'run show'
# scope command when -v is set (Generator/Alloy.hs, header), and the
# committed test/regression/*.als.reg baselines are -v-shaped --
# dropping -v makes every generated .als differ from its baseline at
# the run-command line (found by Frank Zeyda on PR #19; the advisory
# diffRegressions legs masked it).  Gating still happens exactly once,
# in validateAlloyOutput / validateChocoOutput below
# (Sigil-Logic/clafer#16); the -v validator chatter during generation
# is redundant but tolerated for baseline parity until the generator
# coupling is decoupled (decision pending on PR #19).
CLAFER = ../clafer -s -v -k --tooldir=..

# Validators for the generated output (same invocations the compiler's
# own -v flag uses; see runValidate in src/Language/Clafer.hs).
ALLOY_JAR = ../org.alloytools.alloy.dist-6.2.0.jar
CHOCOSOLVER_JAR = ../chocosolver.jar
VALIDATE_ALLOY = java -Djava.awt.headless=true -jar $(ALLOY_JAR) commands
VALIDATE_CHOCO = java -jar $(CHOCOSOLVER_JAR) -v --file

# Validation exclusion lists (Sigil-Logic/clafer#16): one generated-file
# name per line, '#' comments allowed; see the files for per-entry
# provenance.  Exclusions are strict expected failures -- an excluded
# file must exist and must still be rejected by its validator, so a
# fixed model (or a renamed one) fails the harness until its entry is
# removed.
ALLOY_EXCLUDES = alloy-validation-excludes.txt
CHOCO_EXCLUDES = choco-validation-excludes.txt
STRIP_EXCLUDES = sed -e 's/[[:space:]]*\#.*$$//' -e '/^[[:space:]]*$$/d'

# Discovery runs through manifest files rather than pipelines: POSIX sh
# reports only the LAST pipeline command's status, so `find | sort | ...`
# would mask a failing or partially-failing producer and let a gate pass
# green on an empty enumeration (PR #19 Cycle 1, HOARDE Codex).  Each
# manifest is created by find as the sole command of its recipe line
# (status propagates to make directly), sorted in place, and asserted
# non-empty before use.
GEN_MANIFEST = .generate-models.list
ALLOY_MANIFEST = .validate-alloy.list
CHOCO_MANIFEST = .validate-choco.list

.PHONY: test generateAlloyJSHTMLDot validateAlloyOutput validateChocoOutput diffRegressions reg newReg clean

UNAME := $(shell uname | tr "A-Z" "a-z")

ifeq ($(UNAME), darwin)
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \)   | sed s/$(SUITE_DIR)\\///
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \)   | sed s/$(SUITE_DIR)\\///
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \)   | sed s/$(SUITE_DIR)\\///
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \)   | sed s/$(SUITE_DIR)\\///
    XARGS_DIFF_COMMAND := xargs  -I % -L1 diff -w -B  $(SUITE_DIR)/% $(REG_DIR)/%.reg
else
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \) -printf "%f\n"
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \) -printf "%f\n"
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \) -printf "%f\n"
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \) -printf "%f\n"
    XARGS_DIFF_COMMAND := xargs  -i diff -w -B $(REG_DIR)/{}.reg $(SUITE_DIR)/{}
endif


ifeq ($(UNAME), darwin)
    XARGS_CP_REGS :=  xargs  -t -I % -L1 cp  $(SUITE_DIR)/% $(REG_DIR)/%.reg
else
    XARGS_CP_REGS := xargs  -t -i cp $(SUITE_DIR)/{} $(REG_DIR)/{}.reg
endif


test:
	@echo "========================"
	@echo "| Beginning testing of |"
	@echo "========================"
	@$(CLAFER) -V
	$(MAKE) clean
	$(MAKE) generateAlloyJSHTMLDot
	$(MAKE) validateAlloyOutput
	$(MAKE) validateChocoOutput
	$(MAKE) diffRegressions

generateAlloyJSHTMLDot:
	@echo "==================================================================================="
	@echo "| Testing 'Positive' suite - generating Alloy, JavaScript, HTML, and Graph output |"
	@echo "==================================================================================="

	# Compile the positive test suite to Alloy, Choco, HTML, and Graph.
	# Per-model compile failures gate: a non-zero clafer exit makes xargs
	# exit non-zero (123 on GNU xargs, 1 on BSD; both keep processing the
	# remaining models first), failing this target (Sigil-Logic/clafer#16;
	# previously masked by a trailing '; true').  Pathnames travel
	# NUL-delimited so xargs never re-parses blanks or quotes.  Note the
	# backends decline unsupported features (reals, the product operator)
	# with an informative message and exit 0 by design -- those models
	# simply produce no .als/.js and never reach the validation gates.
	@find $(SUITE_DIR) -type f \( -iname "*.cfr" ! -iname "*.des.cfr" \) > $(GEN_MANIFEST)
	@sort -o $(GEN_MANIFEST) $(GEN_MANIFEST)
	@test -s $(GEN_MANIFEST) || { \
		echo "[ERROR] No .cfr models found under $(SUITE_DIR)/."; \
		rm -f $(GEN_MANIFEST); false; \
	}
	@tr '\n' '\000' < $(GEN_MANIFEST) | xargs -0 -n1 $(CLAFER) -m=alloy -m=choco -m=html -m=graph --self-contained; \
	rc=$$?; rm -f $(GEN_MANIFEST); exit $$rc

# Gated Alloy validation (Sigil-Logic/clafer#16): every generated .als
# must be accepted by Alloy 6.2.0 ('commands' parses and type-checks the
# file), except the explicit by-name exclusions in $(ALLOY_EXCLUDES).
# A second pass asserts every exclusion is still an expected failure.
validateAlloyOutput:
	@echo "==========================================================="
	@echo "| Testing 'Positive' suite - validating Alloy output      |"
	@echo "|   (exit-code-gated; exclusions: $(ALLOY_EXCLUDES)) |"
	@echo "==========================================================="

	@if test ! -f "$(ALLOY_JAR)"; then \
		echo "[ERROR] Missing $(ALLOY_JAR)."; false; \
	fi
	@if test ! -f "$(ALLOY_EXCLUDES)"; then \
		echo "[ERROR] Missing $(ALLOY_EXCLUDES)."; false; \
	fi

	@find $(SUITE_DIR) -type f -iname '*.als' > $(ALLOY_MANIFEST)
	@sort -o $(ALLOY_MANIFEST) $(ALLOY_MANIFEST)
	@test -s $(ALLOY_MANIFEST) || { \
		echo "[ERROR] No generated .als files found under $(SUITE_DIR)/ -- did generation run?"; \
		rm -f $(ALLOY_MANIFEST); false; \
	}
	@fails=0; checked=0; skipped=0; \
	while IFS= read -r f; do \
		if $(STRIP_EXCLUDES) $(ALLOY_EXCLUDES) | grep -qxF "$${f#$(SUITE_DIR)/}"; then \
			skipped=$$((skipped+1)); continue; \
		fi; \
		checked=$$((checked+1)); \
		if ! out=$$($(VALIDATE_ALLOY) "$$f" 2>&1); then \
			echo "[FAIL] Alloy 6.2.0 rejects $$f:"; \
			printf '%s\n' "$$out" | sed 's/^/    /'; \
			fails=$$((fails+1)); \
		fi; \
	done < $(ALLOY_MANIFEST); \
	rm -f $(ALLOY_MANIFEST); \
	echo "Alloy validation: $$checked gated ($$((checked-fails)) accepted, $$fails rejected), $$skipped excluded."; \
	[ $$fails -eq 0 ]

	@$(STRIP_EXCLUDES) $(ALLOY_EXCLUDES) | { \
		stale=0; \
		while IFS= read -r name; do \
			f="$(SUITE_DIR)/$$name"; \
			if [ ! -f "$$f" ]; then \
				echo "[STALE] $$name is excluded in $(ALLOY_EXCLUDES) but was not generated"; \
				stale=$$((stale+1)); \
			elif $(VALIDATE_ALLOY) "$$f" >/dev/null 2>&1; then \
				echo "[STALE] $$name is excluded in $(ALLOY_EXCLUDES) but Alloy 6.2.0 now accepts it -- remove the entry"; \
				stale=$$((stale+1)); \
			fi; \
		done; \
		[ $$stale -eq 0 ] || { echo "$$stale stale exclusion(s) in $(ALLOY_EXCLUDES)."; false; }; \
	}

# Gated Choco validation (Sigil-Logic/clafer#16): every generated .js
# must be accepted by chocosolver -v, except the explicit by-name
# exclusions in $(CHOCO_EXCLUDES).  Same strict-exclusion semantics as
# validateAlloyOutput.
validateChocoOutput:
	@echo "==========================================================="
	@echo "| Testing 'Positive' suite - validating Choco output      |"
	@echo "|   (exit-code-gated; exclusions: $(CHOCO_EXCLUDES)) |"
	@echo "==========================================================="

	@if test ! -f "$(CHOCOSOLVER_JAR)"; then \
		echo "[ERROR] Missing $(CHOCOSOLVER_JAR)."; false; \
	fi
	@if test ! -f "$(CHOCO_EXCLUDES)"; then \
		echo "[ERROR] Missing $(CHOCO_EXCLUDES)."; false; \
	fi

	@find $(SUITE_DIR) -type f -iname '*.js' > $(CHOCO_MANIFEST)
	@sort -o $(CHOCO_MANIFEST) $(CHOCO_MANIFEST)
	@test -s $(CHOCO_MANIFEST) || { \
		echo "[ERROR] No generated .js files found under $(SUITE_DIR)/ -- did generation run?"; \
		rm -f $(CHOCO_MANIFEST); false; \
	}
	@fails=0; checked=0; skipped=0; \
	while IFS= read -r f; do \
		if $(STRIP_EXCLUDES) $(CHOCO_EXCLUDES) | grep -qxF "$${f#$(SUITE_DIR)/}"; then \
			skipped=$$((skipped+1)); continue; \
		fi; \
		checked=$$((checked+1)); \
		if ! out=$$($(VALIDATE_CHOCO) "$$f" 2>&1); then \
			echo "[FAIL] chocosolver rejects $$f:"; \
			printf '%s\n' "$$out" | sed 's/^/    /'; \
			fails=$$((fails+1)); \
		fi; \
	done < $(CHOCO_MANIFEST); \
	rm -f $(CHOCO_MANIFEST); \
	echo "Choco validation: $$checked gated ($$((checked-fails)) accepted, $$fails rejected), $$skipped excluded."; \
	[ $$fails -eq 0 ]

	@$(STRIP_EXCLUDES) $(CHOCO_EXCLUDES) | { \
		stale=0; \
		while IFS= read -r name; do \
			f="$(SUITE_DIR)/$$name"; \
			if [ ! -f "$$f" ]; then \
				echo "[STALE] $$name is excluded in $(CHOCO_EXCLUDES) but was not generated"; \
				stale=$$((stale+1)); \
			elif $(VALIDATE_CHOCO) "$$f" >/dev/null 2>&1; then \
				echo "[STALE] $$name is excluded in $(CHOCO_EXCLUDES) but chocosolver now accepts it -- remove the entry"; \
				stale=$$((stale+1)); \
			fi; \
		done; \
		[ $$stale -eq 0 ] || { echo "$$stale stale exclusion(s) in $(CHOCO_EXCLUDES)."; false; }; \
	}

diffRegressions:
	@echo "======================================================="
	@echo "| Testing 'Positive' suite - Diffing with regressions |"
	@echo "======================================================="

	@echo "---------------------"
	@echo "| Alloy regressions |"
	@echo "---------------------"
	@$(FIND_ALS_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "---------------------"
	@echo "| Choco regressions |"
	@echo "---------------------"
	@$(FIND_JS_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "--------------------"
	@echo "| HTML regressions |"
	@echo "--------------------"
	@$(FIND_HTML_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

	@echo "---------------------"
	@echo "| Graph regressions |"
	@echo "---------------------"
	@$(FIND_DOT_COMMAND) | $(XARGS_DIFF_COMMAND) ; true

reg:
	@echo "============================"
	@echo "| Creating new regressions |"
	@echo "============================"
	@rm $(REG_DIR)/*.reg
	$(MAKE) newReg

newReg:
	@echo "---------------------"
	@echo "| Alloy regressions |"
	@echo "---------------------"
	@$(FIND_ALS_COMMAND) | $(XARGS_CP_REGS)
	@echo "---------------------"
	@echo "| Choco regressions |"
	@echo "---------------------"
	@$(FIND_JS_COMMAND) | $(XARGS_CP_REGS)
	@echo "---------------------"
	@echo "| HTML regressions |"
	@echo "---------------------"
	@$(FIND_HTML_COMMAND) | $(XARGS_CP_REGS)
	@echo "----------------------"
	@echo "| Graph regressions |"
	@echo "----------------------"
	@$(FIND_DOT_COMMAND) | $(XARGS_CP_REGS)
	@echo "----------------------------"
	@echo "| Adding to Git repository |"
	@echo "----------------------------"
	@git add $(REG_DIR)/*.reg

# The failing/ directory holds committed fixtures (e.g.,
# gi89-ref-to-constant.js), not generated output -- prune it so clean
# never deletes tracked files (found under Sigil-Logic/clafer#13: every
# `make test` run silently deleted the fixture from the worktree).
clean:
	@echo "==============="
	@echo "| Cleaning up |"
	@echo "==============="
	@echo ""
	@echo 'Removing *.als'
	@find . -path ./failing -prune -o -type f -name '*.als' -print0 | xargs -0 rm -f
	@echo 'Removing *.js'
	@find . -path ./failing -prune -o -type f -name '*.js' -print0 | xargs -0 rm -f
	@echo 'Removing *.html'
	@find . -path ./failing -prune -o -type f -name '*.html' -print0 | xargs -0 rm -f
	@echo 'Removing *.dot'
	@find . -path ./failing -prune -o -type f -name '*.dot' -print0 | xargs -0 rm -f
	@echo 'Removing *.dot.svg'
	@find . -path ./failing -prune -o -type f -name '*.dot.svg' -print0 | xargs -0 rm -f
	@echo 'Removing *~'
	@find . -type f -name '*~' -print0 | xargs -0 rm -f
	@echo 'Removing discovery manifests'
	@rm -f $(GEN_MANIFEST) $(ALLOY_MANIFEST) $(CHOCO_MANIFEST)
