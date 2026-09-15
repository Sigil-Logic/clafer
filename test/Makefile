SUITE_DIR = positive
REG_DIR = regression
# The generation flags are -v-free (Sigil-Logic/clafer#20): 'run show'
# emission no longer depends on -v (decoupled in Generator/Alloy.hs and
# Generator/AlloyLtl.hs, header), and the committed
# test/regression/*.als.reg baselines carry the run command, so plain
# generation reproduces them byte-for-byte.  Do NOT add -v back here:
# since #20 a validator rejection makes clafer itself exit non-zero,
# so a -v generation sweep would fail on the 42 excluded-by-name
# temporal tmp_* models before the gated validation legs run.
# Validator gating happens exactly once, in validateAlloyOutput /
# validateChocoOutput below (Sigil-Logic/clafer#16), with strict
# by-name exclusions; baseline gating happens in diffRegressions
# (Sigil-Logic/clafer#22).
CLAFER = ../clafer -s -k --tooldir=..

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

# Gated-diff manifests (Sigil-Logic/clafer#22): the same manifest
# pattern, one generated-tree/.reg-corpus pair reused by each of the
# four diffRegressions legs in turn; the .names siblings hold the
# prefix-stripped, re-sorted basenames the legs actually compare.
DIFF_GEN_MANIFEST = .diff-generated.list
DIFF_REG_MANIFEST = .diff-baselines.list

.PHONY: test generateAlloyJSHTMLDot validateAlloyOutput validateChocoOutput validateCliGating diffRegressions reg newReg clean

UNAME := $(shell uname | tr "A-Z" "a-z")

ifeq ($(UNAME), darwin)
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \)   | sed s/$(SUITE_DIR)\\///
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \)   | sed s/$(SUITE_DIR)\\///
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \)   | sed s/$(SUITE_DIR)\\///
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \)   | sed s/$(SUITE_DIR)\\///
else
    FIND_ALS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.als" \) -printf "%f\n"
    FIND_JS_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.js" \) -printf "%f\n"
    FIND_HTML_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.html" \) -printf "%f\n"
    FIND_DOT_COMMAND :=  find $(SUITE_DIR)  -type f \( -iname "*.dot" \) -printf "%f\n"
endif

# XARGS_DIFF_COMMAND is gone (Sigil-Logic/clafer#22): the darwin and
# linux variants passed the diff operands in OPPOSITE orders (darwin:
# generated file first; linux: baseline first), and the advisory xargs
# pipeline they fed is replaced by the gated DIFF_LEG loop below --
# one portable codepath, baseline first on both platforms.  The
# FIND_*_COMMAND variables above remain in use by newReg.

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
	$(MAKE) validateCliGating
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
	@echo "=================================================================="
	@echo "| Testing 'Positive' suite - validating Alloy output             |"
	@echo "|   (exit-code-gated; exclusions: $(ALLOY_EXCLUDES)) |"
	@echo "=================================================================="

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
	@echo "=================================================================="
	@echo "| Testing 'Positive' suite - validating Choco output             |"
	@echo "|   (exit-code-gated; exclusions: $(CHOCO_EXCLUDES)) |"
	@echo "=================================================================="

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

# CLI -v gating semantics (Sigil-Logic/clafer#20; regressions for the
# PR #23 HOARDE Codex Cycle 1 findings): -v must propagate a validator
# rejection as a non-zero clafer exit, stay exit 0 on accepted models,
# skip cleanly under console output (-o, which writes no files to
# validate), and must not misread a path containing spaces as a
# rejection (validators are invoked with argument lists via rawSystem,
# not shell-tokenized command strings).  A missing dot executable must
# leave the graph leg advisory (exit 0 with a notice), and the target
# itself must survive a checkout path containing spaces (quoted
# CLI_CLAFER; PR #23 Codex Cycle 2).  The generation-side dot spawn --
# the html graph embedding behind --add-graph -- is advisory the same
# way (Sigil-Logic/clafer#25): a missing dot degrades generation to
# output without the embedded diagram, keeps exit 0, and prints a
# notice on stderr, rather than crashing the whole generation sweep.
# The console-output probe captures the streams separately to pin the
# notice to stderr -- under -o, stdout carries the generated artifact
# itself and must stay uncontaminated (PR #26 Codex Cycle 1).
CLI_CLAFER = "$(CURDIR)/../clafer" -s -k "--tooldir=$(CURDIR)/.."

validateCliGating:
	@echo "=================================================================="
	@echo "| Testing CLI gating semantics (Sigil-Logic/clafer#20, #25)      |"
	@echo "=================================================================="
	@tmp=$$(mktemp -d); \
	status=0; \
	cp $(SUITE_DIR)/i23.cfr $(SUITE_DIR)/tmp_before01.cfr "$$tmp/"; \
	mkdir "$$tmp/with space"; cp $(SUITE_DIR)/i23.cfr "$$tmp/with space/"; \
	if ! (cd "$$tmp" && $(CLI_CLAFER) -v -m=alloy -m=choco i23.cfr >/dev/null 2>&1); then \
		echo "[FAIL] accepted model: clafer -v must exit 0"; status=1; fi; \
	if (cd "$$tmp" && $(CLI_CLAFER) -v -m=alloy tmp_before01.cfr >/dev/null 2>&1); then \
		echo "[FAIL] rejected model: clafer -v must exit non-zero"; status=1; fi; \
	if ! out=$$(cd "$$tmp" && $(CLI_CLAFER) -v -o -m=alloy i23.cfr 2>&1); then \
		echo "[FAIL] console output: clafer -v -o must exit 0"; status=1; \
	elif ! printf '%s\n' "$$out" | grep -q "Validation skipped"; then \
		echo "[FAIL] console output: skip notice missing"; status=1; fi; \
	if ! (cd "$$tmp" && $(CLI_CLAFER) -v -m=alloy -m=choco "with space/i23.cfr" >/dev/null 2>&1); then \
		echo "[FAIL] path with spaces: accepted model must exit 0"; status=1; fi; \
	if ! out=$$(cd "$$tmp" && env PATH=/nonexistent $(CLI_CLAFER) -v -m=graph i23.cfr 2>&1); then \
		echo "[FAIL] missing dot: graph leg must stay advisory (exit 0)"; status=1; \
	elif ! printf '%s\n' "$$out" | grep -q "advisory"; then \
		echo "[FAIL] missing dot: advisory skip notice missing"; status=1; fi; \
	rm -f "$$tmp/i23.html" "$$tmp/i23.dot"; \
	if ! out=$$(cd "$$tmp" && env PATH=/nonexistent $(CLI_CLAFER) -m=html -m=graph --self-contained --add-graph i23.cfr 2>&1); then \
		echo "[FAIL] missing dot: html graph embedding must degrade (exit 0)"; status=1; \
	elif ! printf '%s\n' "$$out" | grep -q "Graph embedding skipped"; then \
		echo "[FAIL] missing dot: embedding skip notice missing"; status=1; \
	elif [ ! -s "$$tmp/i23.html" ] || [ ! -s "$$tmp/i23.dot" ]; then \
		echo "[FAIL] missing dot: degraded generation must still write outputs"; status=1; fi; \
	if ! out=$$(cd "$$tmp" && env PATH=/nonexistent $(CLI_CLAFER) -o -m=html -m=graph --self-contained --add-graph i23.cfr 2>"$$tmp/probe7-err.txt"); then \
		echo "[FAIL] missing dot: -o generation must degrade (exit 0)"; status=1; \
	elif ! grep -q "Graph embedding skipped" "$$tmp/probe7-err.txt"; then \
		echo "[FAIL] missing dot: -o advisory notice missing from stderr"; status=1; \
	elif printf '%s\n' "$$out" | grep -q "Graph embedding skipped"; then \
		echo "[FAIL] missing dot: advisory notice contaminates stdout"; status=1; \
	elif ! printf '%s\n' "$$out" | grep -q "digraph"; then \
		echo "[FAIL] missing dot: -o stdout must still carry generated output"; status=1; fi; \
	rm -rf "$$tmp"; \
	if [ $$status -eq 0 ]; then echo "CLI gating: 7 probes passed."; fi; \
	[ $$status -eq 0 ]

# One gated diff leg (Sigil-Logic/clafer#22): $(call DIFF_LEG,<ext>,<label>)
# expands to the canned recipe for one output kind.  Discovery follows
# the #16/#19 manifest pattern: find runs as the sole command of its
# line so a failing producer fails the leg directly, the name lists
# are re-sorted after prefix/suffix stripping (stripping .reg is not
# order-preserving), and both lists are asserted non-empty.  The
# generated tree and the .reg corpus are then compared BOTH ways with
# comm -- a generated file with no baseline, or a baseline with no
# generated counterpart, fails the leg rather than warning -- and
# each surviving pair is diffed with the whitespace-insensitive flags
# retained from the advisory era (diff -w -B).  Every divergence in a
# leg is printed before the leg fails, so one run shows the leg's
# full drift picture.
define DIFF_LEG
@echo "---------------------"
@echo "| $(2) regressions |"
@echo "---------------------"
@find $(SUITE_DIR) -type f -iname '*.$(1)' > $(DIFF_GEN_MANIFEST)
@sed 's|^$(SUITE_DIR)/||' $(DIFF_GEN_MANIFEST) > $(DIFF_GEN_MANIFEST).names
@sort -o $(DIFF_GEN_MANIFEST).names $(DIFF_GEN_MANIFEST).names
@test -s $(DIFF_GEN_MANIFEST).names || { \
	echo "[ERROR] No generated .$(1) files found under $(SUITE_DIR)/ -- did generation run?"; \
	rm -f $(DIFF_GEN_MANIFEST) $(DIFF_GEN_MANIFEST).names; false; \
}
@find $(REG_DIR) -type f -iname '*.$(1).reg' > $(DIFF_REG_MANIFEST)
@sed -e 's|^$(REG_DIR)/||' -e 's|\.reg$$||' $(DIFF_REG_MANIFEST) > $(DIFF_REG_MANIFEST).names
@sort -o $(DIFF_REG_MANIFEST).names $(DIFF_REG_MANIFEST).names
@test -s $(DIFF_REG_MANIFEST).names || { \
	echo "[ERROR] No .$(1).reg baselines found under $(REG_DIR)/."; \
	rm -f $(DIFF_GEN_MANIFEST) $(DIFF_GEN_MANIFEST).names $(DIFF_REG_MANIFEST) $(DIFF_REG_MANIFEST).names; false; \
}
@status=0; fails=0; compared=0; \
if ! only_gen=$$(comm -23 $(DIFF_GEN_MANIFEST).names $(DIFF_REG_MANIFEST).names); then \
	echo "[ERROR] comm failed comparing the .$(1) name lists"; status=1; \
fi; \
if ! only_reg=$$(comm -13 $(DIFF_GEN_MANIFEST).names $(DIFF_REG_MANIFEST).names); then \
	echo "[ERROR] comm failed comparing the .$(1) name lists"; status=1; \
fi; \
if [ -n "$$only_gen" ]; then \
	echo "[FAIL] Generated .$(1) file(s) with no $(REG_DIR)/ baseline (run 'make reg' if the new output is intended):"; \
	printf '%s\n' "$$only_gen" | sed 's/^/    /'; status=1; \
fi; \
if [ -n "$$only_reg" ]; then \
	echo "[FAIL] .$(1).reg baseline(s) with no generated counterpart (stale corpus entry, or output lost):"; \
	printf '%s\n' "$$only_reg" | sed 's/^/    /'; status=1; \
fi; \
while IFS= read -r name; do \
	[ -f "$(REG_DIR)/$$name.reg" ] || continue; \
	compared=$$((compared+1)); \
	if ! out=$$(diff -w -B "$(REG_DIR)/$$name.reg" "$(SUITE_DIR)/$$name"); then \
		echo "[FAIL] $$name diverges from $(REG_DIR)/$$name.reg:"; \
		printf '%s\n' "$$out" | sed 's/^/    /'; \
		fails=$$((fails+1)); \
	fi; \
done < $(DIFF_GEN_MANIFEST).names; \
rm -f $(DIFF_GEN_MANIFEST) $(DIFF_GEN_MANIFEST).names $(DIFF_REG_MANIFEST) $(DIFF_REG_MANIFEST).names; \
echo "$(2) regressions: $$compared compared, $$fails divergent."; \
[ $$status -eq 0 ] && [ $$fails -eq 0 ]
endef

# Gated regression diff (Sigil-Logic/clafer#22): these four legs used
# to end in '; true', so baseline drift was printed but never failed
# make test -- on PR #19 a corpus-wide .als drift sailed through a
# green run and was caught only by eye.  Each leg now fails on any
# divergence from the committed .reg corpus and on any counterpart
# mismatch in either direction.  Declining is backend-specific
# (Sigil-Logic/clafer#16): a model using features a backend does not
# support exits 0 producing no output file for that backend only.  At
# the time of writing, Alloy declines 5 models (mergeExpAndSetExp,
# objectivesMinMax, primitiveTypesAndCoersions, product, reals),
# Choco declines 3 of those (all but objectivesMinMax and product)
# and also emits no .js for the 42 temporal tmp_* models, and the
# HTML and Graph backends decline none -- hence the per-extension
# counts: 157 .als / 117 .js / 162 .html / 162 .dot.  A declined
# model is absent from BOTH the generated tree and the .reg corpus of
# its declining leg, so the counterpart invariant -- which relates
# those two trees, not the .cfr suite -- needs no decliner carve-out.
# For INTENDED output changes, see the re-baselining workflow
# documented above the reg target.
diffRegressions:
	@echo "======================================================="
	@echo "| Testing 'Positive' suite - Diffing with regressions |"
	@echo "======================================================="
	$(call DIFF_LEG,als,Alloy)
	$(call DIFF_LEG,js,Choco)
	$(call DIFF_LEG,html,HTML)
	$(call DIFF_LEG,dot,Graph)

# Re-baselining workflow for INTENDED output changes
# (Sigil-Logic/clafer#22): diffRegressions gates on the committed
# .reg corpus, so a change that legitimately alters generated output
# must refresh the corpus in the same change set:
#
#   1. make test        -- fails in diffRegressions, printing the drift
#   2. review every printed hunk: each must be explained by the change
#      at hand (an unexplained hunk is a real regression, not a
#      re-baselining candidate)
#   3. make reg         -- wipes regression/*.reg, re-copies every
#      generated file from positive/ as its new baseline, and stages
#      the result (git add)
#   4. make test        -- must now pass end to end
#   5. commit the .reg deltas TOGETHER with the code change; the
#      baseline diff is reviewed as part of the PR
#
# reg rebuilds the corpus from whatever is in positive/, so run it
# only right after a full generation sweep over a clean tree (make
# test runs clean + generateAlloyJSHTMLDot first); a partial tree
# would silently shrink the corpus -- which the reverse counterpart
# gate in DIFF_LEG then catches on the next run.
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
	@rm -f $(GEN_MANIFEST) $(ALLOY_MANIFEST) $(CHOCO_MANIFEST) \
		$(DIFF_GEN_MANIFEST) $(DIFF_GEN_MANIFEST).names \
		$(DIFF_REG_MANIFEST) $(DIFF_REG_MANIFEST).names
